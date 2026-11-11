import EraSpec.Protocol.InteropAtomicity.Specs.Pause

/-!
# Properties: pausing delays atomic flows and never unwinds them

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.Pause`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.Pause`.

## The four claims

1. **Safety is unaffected.**  A pause gate can only reject a step, and the `pause`/`unpause`
   steps write no manager state.  So every paused run's manager trace is a `RunLog`
   (`Properties.PausedRunIsRunLog`), and its `authorizeRefund` calls form a `ReachLog`
   (`Properties.PausedRunAuthCallsReachLog`).  The same holds with each chain's tree attached:
   a paused `PSysSteps` run is a `Contracts.AppendPath.SysSteps` run with the same logs
   (`Properties.PausedSystemIsSystemRun`).  The headline safety results then hold verbatim over
   paused runs, with the same conclusions and no extra premise:
   `ExecutedObligationNeverRefundedOrBreakUnderPause`,
   `OneExecutionFreezesTheFlowOrBreakUnderPause`, `NoneOrAllOrBreakUnderPause` (and its
   pinned form), `LoggedExecutionExcludesLoggedRefundOrBreakUnderPause`,
   `ExecutedImpliesRealFlowFinalizableOrLoggedClashUnderPause`, `SystemOncePerLegUnderPause`
   and `SystemExecutedObligationNeverRefundedOrBreakUnderPause`.  Conversely, with every flag
   clear the paused models are exactly `RunLog` and `SysSteps`
   (`Properties.RunLogIsUnpausedRun`, `Properties.SystemRunIsUnpausedSystemRun`), so the flags
   are the only difference.
2. **A paused destination leaves a committed flow stuck.**  Take a flow whose legs were all
   committed by on-time batches.  While the destination vault of one of its legs is paused,
   that leg cannot execute.  No leg of the flow can be refunded either: no absence proof for a
   committed leg passes the timeout gate unless it carries a located break, and a refund
   authorized under another flow's preimage is a logged clash
   (`Properties.PausedDestinationLeavesFlowStuck`).  Pause therefore never opens the refund
   path of a committed flow.  A pause on the source side before a leg is committed is
   different: it blocks the `append` (`Properties.PausedCenterStaysPausedAlongRuns`).  If it
   lasts past the deadline, the leg is never committed in time, and the timeout is genuine.
   That consequence is not a theorem here, because the history `System` is fixed and not tied
   to the run's appends.  The source finding behind the wording: the L2 interop handler has no pause gate
   (`_ensureNotPaused` is a no-op on L2).  So in this model the destination pause that can
   block an atomic execution is the vault's, reached through the bundle's own calls
   (`Properties.PauseGatesReadOnlyTheirOwnFlags`).  While the destination vault stays paused,
   no bundle that mints through it executes, whatever else the run does
   (`Properties.PausedDestinationStaysPausedAlongRuns`).  So a pause that is never lifted
   strands such a leg for good, with no refund path, even after a sibling leg of the same flow
   was delivered elsewhere (`Properties.PermanentDestinationPauseStrandsLeg`,
   `Properties.DestinationPauseStrandsSiblingWitness`).  Liveness of a committed flow rests on
   the destination vault's owner (`OPS-CONFIG`).
3. **Unpausing restores enabledness.**  After the destination vault is unpaused, the gate is
   exactly the unpaused gate (`Properties.UnpausedGateIsTheGate`).  From every reachable state,
   at most one `unpause` followed by the execution is a run, on presentable evidence, under data
   availability (`Properties.UnpauseRestoresExecution`).  The gate has no clock (see the Specs
   header), so a long pause delays the execution but cannot expire it.
4. **A paused source vault blocks the refund claim, and the claim can be retried.**  While the
   source vault stays paused, a `Revertable` leg whose bundle has a router call stays
   `Revertable` and is never claimed (`Properties.PausedVaultKeepsLegRevertable`).  From every
   reachable state, at most one `unpause` followed by the claim is a run
   (`Properties.UnpauseReEnablesClaim`).  That the concrete claim then succeeds is a property of
   the bundle's calls, not of the pause: see
   `Contracts.AssetRouter.PausedRecovery` for the router-and-vault refund itself.

## Witnesses

`Properties.PauseRunWitness` is one run from fresh storage with every kind of step, including
two pauses and two unpauses.  `Properties.PausedDestinationStuckWitness` and
`Properties.PausedVaultClaimWitness` are states inside that run where the pause premises hold,
the break disjuncts are false, and unpausing then completes the step.
`Properties.DestinationPauseStrandsSiblingWitness` is a two-leg flow, committed on two chains,
with one leg delivered and the other stranded by its destination's pause.
`Properties.LoggedExecutionExcludesLoggedRefundOrBreakUnderPauseWitness` and
`Properties.PausedSystemWitness` lift `Contracts.FlowBinding`'s padding witness and
`Contracts.AppendPath`'s system witness to paused runs.
-/

namespace Contracts.InteropPause

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Refund
open Contracts.FlowBinding Contracts.AtomicFlowManager

/-! ## 1. Pause only removes steps -/

/-- **A PAUSED RUN IS A RUN.**  Forgetting the flags maps every paused run to a `RunLog`
between the same manager states, whose log is the run's `_checkFlowId` calls. -/
def Properties.PausedRunIsRunLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (X Y : PState) (tr : List Action),
    PRun h z0 hl cv fh S prof X Y tr → RunLog h z0 hl cv fh S X.mgrs Y.mgrs (checkedCalls tr)

/-- **ITS REFUND AUTHORIZATIONS ARE A `ReachLog`.**  So every `Contracts.Refund` result over
`ReachLog` applies to a paused run. -/
def Properties.PausedRunAuthCallsReachLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (X Y : PState) (tr : List Action),
    PRun h z0 hl cv fh S prof X Y tr →
      ReachLog h z0 hl cv fh S X.mgrs Y.mgrs (authCalls (checkedCalls tr))

/-- **WITH NOTHING PAUSED, NOTHING IS LOST.**  Every `RunLog` is a paused run on which every
flag stays clear, with the same calls. -/
def Properties.RunLogIsUnpausedRun : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (Ms Ns : Managers) (log : List CheckedCall),
    RunLog h z0 hl cv fh S Ms Ns log →
      ∃ tr, PRun h z0 hl cv fh S prof ⟨Ms, noFlags⟩ ⟨Ns, noFlags⟩ tr ∧ checkedCalls tr = log

/-- **A PAUSED EXECUTION IS AN EXECUTION.** -/
def Properties.PausedExecutionIsExecution : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (P : Flags) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaPausedBy h z0 hl cv fh S prof P F ev leg → ExecutedViaBy h z0 hl cv fh S F ev leg

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED, OR A LOCATED BREAK, UNDER PAUSE.**
`Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak`, verbatim, over every
paused run from fresh managers and any initial flags.  Its log is the run's
`authorizeRefund` calls. -/
def Properties.ExecutedObligationNeverRefundedOrBreakUnderPause : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (prof : Profile) (P₀ : Flags) (Y : PState) (tr : List Action),
      PRun h z0 hl cv fh S prof ⟨emptyManagers, P₀⟩ Y tr →
      ¬ Refunded Y.mgrs (obligationOf F leg)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) (authCalls (checkedCalls tr))

/-- **ONE EXECUTION FREEZES THE FLOW, OR A LOCATED BREAK, UNDER PAUSE.**
`Contracts.Refund.Properties.OneExecutionFreezesTheFlowOrBreak`, verbatim, over paused runs. -/
def Properties.OneExecutionFreezesTheFlowOrBreakUnderPause : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (prof : Profile) (P₀ : Flags) (Y : PState) (tr : List Action),
      PRun h z0 hl cv fh S prof ⟨emptyManagers, P₀⟩ Y tr →
    ∀ other ∈ F.legs,
      ¬ Refunded Y.mgrs (obligationOf F other)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F other) (authCalls (checkedCalls tr))

/-- **NONE OR ALL, OR A LOCATED BREAK, UNDER PAUSE.**
`Contracts.Atomicity.Properties.NoneOrAllOrBreak`, with execution through the gate under any
pause flags.  Finalizability does not depend on the flags. -/
def Properties.NoneOrAllOrBreakUnderPause : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (prof : Profile) (P : Flags) (F : Flow) (ev : GateEvidence),
      FlowFinalizableBy h z0 hl cv S A F
        ∨ (∀ leg, ¬ ExecutedViaPausedBy h z0 hl cv fh S prof P F ev leg)
        ∨ GateBreak h z0 hl S F ev

/-- **NONE OR ALL, OR A BREAK ON THE FIRST STRANDED LEG, UNDER PAUSE.**
`Contracts.Atomicity.Properties.NoneOrAllOrBreakPinned`, likewise. -/
def Properties.NoneOrAllOrBreakPinnedUnderPause : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (prof : Profile) (P : Flags) (F : Flow) (ev : GateEvidence),
      FlowFinalizableBy h z0 hl cv S A F
        ∨ (∀ leg, ¬ ExecutedViaPausedBy h z0 hl cv fh S prof P F ev leg)
        ∨ PinnedGateBreak h z0 hl cv S A F ev

/-- **A LOGGED EXECUTION AND A LOGGED REFUND OF ONE FLOW ID, UNDER PAUSE.**
`Contracts.FlowBinding.Properties.LoggedExecutionExcludesLoggedRefundOrBreak`, verbatim, over
paused runs: a located break on one of the two calls' proofs, or a logged clash. -/
def Properties.LoggedExecutionExcludesLoggedRefundOrBreakUnderPause : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (prof : Profile) (X Y : PState) (tr : List Action),
    PRun h z0 hl cv fh S prof X Y tr →
    ∀ (e : ExecCall), Action.execute e ∈ tr →
    ∀ (a : AuthCall), Action.authorize a ∈ tr → a.flow.flowId = e.flow.flowId →
      InclusionBreak h z0 hl S a.missing.chain (e.evidence a.missing).1 (e.evidence a.missing).2
        ∨ AbsenceBreak h z0 hl S a.flow.deadline a.missing.chain a.batch a.proof
        ∨ FlowIdClash fh e.flow a.flow

/-- **PARTIAL ATOMICITY OVER THE REAL FLOW, UNDER PAUSE.**
`Contracts.FlowBinding.Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClash`, verbatim,
over paused runs. -/
def Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClashUnderPause : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (prof : Profile) (X Y : PState) (tr : List Action), PRun h z0 hl cv fh S prof X Y tr →
    ∀ (e : ExecCall), Action.execute e ∈ tr →
    ∀ c ∈ checkedCalls tr, c.flow.flowId = e.flow.flowId →
      FlowFinalizableBy h z0 hl cv S A c.flow
        ∨ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
        ∨ FlowIdClash fh e.flow c.flow

/-- **THE SAME WITH EACH CHAIN'S TREE ATTACHED.**  Forgetting the flags maps every paused
tree-attached system run to a `Contracts.AppendPath.SysSteps` run with the same logs. -/
def Properties.PausedSystemIsSystemRun : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (X Y : PSysState) (log : List Obligation) (alog : List AuthCall),
    PSysSteps h z0 hl cv fh S prof X Y log alog →
      Contracts.AppendPath.SysSteps h z0 hl cv fh S X.chains Y.chains log alog

/-- **…AND WITH NOTHING PAUSED, NOTHING IS LOST.** -/
def Properties.SystemRunIsUnpausedSystemRun : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (X Y : Contracts.AppendPath.Chains) (log : List Obligation)
    (alog : List AuthCall),
    Contracts.AppendPath.SysSteps h z0 hl cv fh S X Y log alog →
      PSysSteps h z0 hl cv fh S prof ⟨X, noFlags⟩ ⟨Y, noFlags⟩ log alog

/-- **ONCE PER LEG, SYSTEM-WIDE, UNDER PAUSE.**
`Contracts.AppendPath.Properties.SystemOncePerLeg`, verbatim, over paused tree-attached runs from
genesis and any initial flags. -/
def Properties.SystemOncePerLegUnderPause : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (P₀ : Flags) (Y : PSysState) (log : List Obligation) (alog : List AuthCall),
    PSysSteps h z0 hl cv fh S prof ⟨Contracts.AppendPath.genesisAll, P₀⟩ Y log alog →
      log.Nodup
        ∧ (∀ o ∈ log, ∃! i, i < (Y.chains o.chain).tree.leafCount
            ∧ ((Y.chains o.chain).tree.leaf i).value = Contracts.AppendPath.commitOf cv o)
        ∧ (∀ o ∈ log, ∀ o' ∈ log, o.chain = o'.chain →
            Contracts.AppendPath.commitOf cv o = Contracts.AppendPath.commitOf cv o' → o = o')

/-- **THE REFUND MILESTONE FOR THE SYSTEM WITH TREES, UNDER PAUSE.**
`Contracts.AppendPath.Properties.SystemExecutedObligationNeverRefundedOrBreak`, verbatim, over
paused tree-attached runs. -/
def Properties.SystemExecutedObligationNeverRefundedOrBreakUnderPause : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System), Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (prof : Profile) (P₀ : Flags) (Y : PSysState) (log : List Obligation) (alog : List AuthCall),
      PSysSteps h z0 hl cv fh S prof ⟨Contracts.AppendPath.genesisAll, P₀⟩ Y log alog →
        ¬ Refunded (Contracts.AppendPath.Chains.mgrs Y.chains) (obligationOf F leg)
          ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog

/-- **EACH GATE READS ONLY ITS OWN FLAGS, AND NO HANDLER FLAG EXISTS.**  Two flag
assignments that agree on the flags a gate reads give the gate the same verdict:

* the execution gate reads only the destination vault's flag, and only for a bundle that
  mints through it, so a bundle that does not is executable under every assignment;
* the refund gate reads only the source vault's flag, and only for a bundle with a router
  call;
* the send gate reads only the source chain's center, router and vault flags. -/
def Properties.PauseGatesReadOnlyTheirOwnFlags : Prop :=
  ∀ (prof : Profile) (P P' : Flags) (c : Chain) (b : UInt256),
    ((prof.mintsViaVault b = true → P (prof.dest b) .vault = P' (prof.dest b) .vault) →
        (ExecOpen prof P b ↔ ExecOpen prof P' b))
    ∧ (prof.mintsViaVault b = false → ExecOpen prof P b)
    ∧ ((prof.recoversViaVault b = true → P c .vault = P' c .vault) →
        (RecoverOpen prof P c b ↔ RecoverOpen prof P' c b))
    ∧ ((∀ k, P c k = P' c k) → (SendOpen prof P c b ↔ SendOpen prof P' c b))

/-! ## 2. A paused destination leaves a committed flow stuck -/

/-- **A COMMITTED FLOW HAS NO VALID TIMEOUT EVIDENCE, OR THE EVIDENCE CARRIES A BREAK.**  If
every leg of `F` is committed by an on-time batch, then no timeout evidence `(N, q)` for any
leg of `F` passes the timeout gate, unless `q` carries a located `AbsenceBreak`. -/
def Properties.CommittedOnTimeExcludesRefundOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (F : Flow), CommittedOnTime cv S F → ∀ other ∈ F.legs, ∀ (N : ℕ) (q : ImtProof),
      ¬ LegRefundableBy h z0 hl cv S F other N q
        ∨ AbsenceBreak h z0 hl S F.deadline other.chain N q

/-- **…SO NO OBLIGATION OF IT IS EVER REFUNDED, OR A LOCATED BREAK.**  If every leg of the
checked flow `F` is committed by an on-time batch, then in every paused run from fresh managers,
every obligation with `F`'s id stays at `Committed` or below, or a call in the run's own log that
marked it carries a `CommittedRefundBreak`. -/
def Properties.CommittedOnTimeNeverRefundedOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow), CommittedOnTime cv S F → FlowIdChecked fh F →
    ∀ (prof : Profile) (P₀ : Flags) (Y : PState) (tr : List Action),
      PRun h z0 hl cv fh S prof ⟨emptyManagers, P₀⟩ Y tr →
    ∀ (o : Obligation), o.flowId = F.flowId →
      ¬ Refunded Y.mgrs o ∨ CommittedRefundBreak h z0 hl fh S F o (authCalls (checkedCalls tr))

/-- **HEADLINE 2: A PAUSED DESTINATION LEAVES A COMMITTED FLOW STUCK.**  Premises: a
well-formed history; a checked flow `F` whose legs are all committed by on-time batches; a leg
`leg` of `F` whose bundle mints through its destination's vault; and a paused run from fresh
managers to a state `Y` in which that vault is paused.  Then at `Y`:

* `leg` cannot execute, on any evidence;
* no obligation of `F` has been refunded, unless a logged call that marked it carries a
  `CommittedRefundBreak`;
* no timeout evidence for any leg of `F` passes the timeout gate, unless it carries an
  `AbsenceBreak`.

So the funds are held, neither delivered nor returned, until the vault is unpaused
(`Properties.UnpauseRestoresExecution`).  Pause never opens the refund path. -/
def Properties.PausedDestinationLeavesFlowStuck : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (leg : FlowLeg), CommittedOnTime cv S F → FlowIdChecked fh F →
    leg ∈ F.legs →
    ∀ (prof : Profile) (P₀ : Flags) (Y : PState) (tr : List Action),
      PRun h z0 hl cv fh S prof ⟨emptyManagers, P₀⟩ Y tr →
      prof.mintsViaVault leg.bundleHash = true →
      Y.flags (prof.dest leg.bundleHash) .vault = true →
        (∀ ev : GateEvidence, ¬ ExecutedViaPausedBy h z0 hl cv fh S prof Y.flags F ev leg)
        ∧ ∀ other ∈ F.legs,
            (¬ Refunded Y.mgrs (obligationOf F other)
              ∨ CommittedRefundBreak h z0 hl fh S F (obligationOf F other)
                  (authCalls (checkedCalls tr)))
            ∧ ∀ (N : ℕ) (q : ImtProof),
                ¬ LegRefundableBy h z0 hl cv S F other N q
                  ∨ AbsenceBreak h z0 hl S F.deadline other.chain N q

/-- **WHILE THE DESTINATION VAULT STAYS PAUSED, NOTHING MINTS THROUGH IT.**  In a paused run
that starts with chain `d`'s vault paused and contains no `unpause` of it, the vault is still
paused at the end, and no logged execution is of a bundle that mints through chain `d`'s vault. -/
def Properties.PausedDestinationStaysPausedAlongRuns : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (X Y : PState) (tr : List Action) (d : Chain),
    PRun h z0 hl cv fh S prof X Y tr → X.flags d .vault = true → Action.unpause d .vault ∉ tr →
      Y.flags d .vault = true
        ∧ ∀ e, Action.execute e ∈ tr → prof.mintsViaVault e.leg.bundleHash = true →
            prof.dest e.leg.bundleHash ≠ d

/-- **WHILE A SOURCE CENTER STAYS PAUSED, NOTHING IS SENT FROM ITS CHAIN.**  In a paused run
that starts with chain `c`'s `InteropCenter` paused and contains no `unpause` of it, the center
is still paused at the end, and no `append` on chain `c` is logged (`sendMessage` and
`sendBundle` are `whenNotPaused`, `InteropCenter.sol:217, 266`). -/
def Properties.PausedCenterStaysPausedAlongRuns : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (X Y : PState) (tr : List Action) (c : Chain),
    PRun h z0 hl cv fh S prof X Y tr → X.flags c .center = true → Action.unpause c .center ∉ tr →
      Y.flags c .center = true ∧ ∀ c' f b, Action.append c' f b ∈ tr → c' ≠ c

/-- **A DESTINATION PAUSE THAT IS NEVER LIFTED STRANDS THE LEG FOR AS LONG AS IT LASTS.**
Premises: a well-formed history; a checked flow `F` whose legs are all committed by on-time
batches; a leg `leg` of `F` whose bundle mints through its destination's vault; a paused run
from fresh managers to `X`, at which that vault is paused.  Then in every continuation from `X`
that never unpauses it:

* no execution of a bundle with `leg`'s hash is logged;
* no obligation of `F` is ever refunded, unless a logged call that marked it carries a
  `CommittedRefundBreak`.

So if another leg of `F` executed, on a destination that is not paused, the outcome stays mixed
while the pause lasts: one leg delivered, and `leg`'s funds burned at the source, neither minted
nor returned.  The protocol offers no exit from this.  The timeout cannot be proven, because `leg`
was committed in time.  Only the destination vault's owner can end it, by unpausing.
`Properties.DestinationPauseStrandsSiblingWitness` is such a run. -/
def Properties.PermanentDestinationPauseStrandsLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (leg : FlowLeg), CommittedOnTime cv S F → FlowIdChecked fh F →
    leg ∈ F.legs →
    ∀ (prof : Profile) (P₀ : Flags) (X : PState) (tr₀ : List Action),
      PRun h z0 hl cv fh S prof ⟨emptyManagers, P₀⟩ X tr₀ →
      prof.mintsViaVault leg.bundleHash = true →
      X.flags (prof.dest leg.bundleHash) .vault = true →
    ∀ (Y : PState) (tr : List Action), PRun h z0 hl cv fh S prof X Y tr →
      Action.unpause (prof.dest leg.bundleHash) .vault ∉ tr →
        (∀ e, Action.execute e ∈ tr → e.leg.bundleHash ≠ leg.bundleHash)
        ∧ ∀ other ∈ F.legs,
            ¬ Refunded Y.mgrs (obligationOf F other)
              ∨ CommittedRefundBreak h z0 hl fh S F (obligationOf F other)
                  (authCalls (checkedCalls (tr ++ tr₀)))

/-! ## 3. Unpausing restores enabledness -/

/-- **AFTER UNPAUSE, THE GATE IS THE UNPAUSED GATE.**  With the leg's destination vault
unpaused, execution under pause is exactly execution through the deployed gate, whatever the
other flags are. -/
def Properties.UnpausedGateIsTheGate : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (P : Flags) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaPausedBy h z0 hl cv fh S prof (P.set (prof.dest leg.bundleHash) .vault false) F ev leg
      ↔ ExecutedViaBy h z0 hl cv fh S F ev leg

/-- **HEADLINE 3: UNPAUSING RESTORES EXECUTION, AT ANY TIME.**  Premises: a well-formed
history with data availability; a checked flow `F` whose legs are all committed by on-time
batches; a leg `leg` of `F`; and any paused run from `X` to `Y`.  Then there is gate evidence
`ev` that a prover can present for every leg, and an extension of the run by at most one
`unpause` of the leg's destination vault followed by the execution of `leg` on `ev`.  The
extension leaves every manager and every other flag as at `Y`.

`Y` is arbitrary, so this holds however long the vault was paused and however many other steps
happened meanwhile.  The gate has no clock, so the deadline having passed does not matter. -/
def Properties.UnpauseRestoresExecution : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (leg : FlowLeg), CommittedOnTime cv S F → FlowIdChecked fh F → leg ∈ F.legs →
    ∀ (prof : Profile) (X Y : PState) (tr : List Action), PRun h z0 hl cv fh S prof X Y tr →
      ∃ (ev : GateEvidence) (Z : PState) (tr' : List Action),
        (∀ l ∈ F.legs, A l.chain (ev l).1 (ev l).2)
        ∧ (∀ a ∈ tr', a = Action.unpause (prof.dest leg.bundleHash) .vault)
        ∧ PRun h z0 hl cv fh S prof X Z (Action.execute ⟨F, ev, leg⟩ :: (tr' ++ tr))
        ∧ Z.mgrs = Y.mgrs ∧ Z.flags (prof.dest leg.bundleHash) .vault = false
        ∧ ∀ c k, ¬ (c = prof.dest leg.bundleHash ∧ k = .vault) → Z.flags c k = Y.flags c k

/-! ## 4. A paused source vault blocks the claim, and the claim can be retried -/

/-- **HEADLINE 4a: WHILE THE SOURCE VAULT STAYS PAUSED, A REVERTABLE LEG STAYS REVERTABLE.**
In a paused run that starts with chain `c`'s vault paused and contains no `unpause` of it, a leg
`⟨f, b, c⟩` that is `Revertable` at the start, and whose bundle has a router call, is still
`Revertable` at the end and was never claimed.  Every `claimRefund` attempt reverts and leaves
it so (`claimRefund` is one transaction, `AtomicFlowManager.sol:165-180`). -/
def Properties.PausedVaultKeepsLegRevertable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (X Y : PState) (tr : List Action) (c : Chain) (f b : UInt256),
    PRun h z0 hl cv fh S prof X Y tr → prof.recoversViaVault b = true →
    X.flags c .vault = true → Action.unpause c .vault ∉ tr →
    stateOf X.mgrs ⟨f, b, c⟩ = .Revertable →
      stateOf Y.mgrs ⟨f, b, c⟩ = .Revertable ∧ Y.flags c .vault = true
        ∧ Action.claim c f b ∉ tr

/-- **HEADLINE 4b: UNPAUSING RE-ENABLES THE CLAIM.**  From every reachable state in which leg
`⟨f, b, c⟩` is `Revertable`, an extension of the run by at most one `unpause` of chain `c`'s
vault followed by its `claimRefund` is a run, and it leaves the leg `Reverted`.  The flags other
than that vault's are as at `Y`. -/
def Properties.UnpauseReEnablesClaim : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (prof : Profile) (X Y : PState) (tr : List Action) (c : Chain) (f b : UInt256),
    PRun h z0 hl cv fh S prof X Y tr → stateOf Y.mgrs ⟨f, b, c⟩ = .Revertable →
      ∃ (Z : PState) (tr' : List Action),
        (∀ a ∈ tr', a = Action.unpause c .vault)
        ∧ PRun h z0 hl cv fh S prof X Z (Action.claim c f b :: (tr' ++ tr))
        ∧ stateOf Z.mgrs ⟨f, b, c⟩ = .Reverted ∧ Z.flags c .vault = false
        ∧ ∀ c' k, ¬ (c' = c ∧ k = .vault) → Z.flags c' k = Y.flags c' k

/-! ## Witnesses -/

/-- **ONE PAUSED RUN WITH EVERY KIND OF STEP.**  For every node hash, leaf hash and padding
constant: the well-formed `mixedSystem 1` with honest access (so data availability holds), and a
paused run from fresh managers with all flags clear.  It appends and authorizes the timed-out
obligation `⟨1, 2, 1⟩` of `mixedFlow 1 1 2`; pauses the destination vault (chain `7`) and the
source vault (chain `1`); unpauses the destination and executes the one leg of the committed flow
`subsetFlow 0 1`; then unpauses the source and claims `⟨1, 2, 1⟩`.

The premises of the section-1 results hold together with a non-empty authorization log, the
executed flow is finalizable with no `GateBreak`, its obligation carries no `RefundBreak` and is
not refunded, and the other obligation ends `Reverted`. -/
def Properties.PauseRunWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (prof : Profile)
      (Y : PState) (tr : List Action) (F : Flow) (ev : GateEvidence) (leg : FlowLeg)
      (o : Obligation),
      Wf S ∧ DataAvailable h z0 hl S A
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩ Y tr
        ∧ (∃ c k, Action.pause c k ∈ tr) ∧ (∃ c k, Action.unpause c k ∈ tr)
        ∧ Action.execute ⟨F, ev, leg⟩ ∈ tr ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ authCalls (checkedCalls tr) ≠ []
        ∧ FlowFinalizableBy h z0 hl cv S A F ∧ ¬ GateBreak h z0 hl S F ev
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) (authCalls (checkedCalls tr))
        ∧ ¬ Refunded Y.mgrs (obligationOf F leg)
        ∧ stateOf Y.mgrs o = .Reverted

/-- **HEADLINES 2 AND 3, ON ONE STATE.**  For every node hash, leaf hash and padding constant,
inside the run of `Properties.PauseRunWitness`: the state after both pauses satisfies every
premise of `Properties.PausedDestinationLeavesFlowStuck` and of
`Properties.UnpauseRestoresExecution`, with a non-empty authorization log.  On that state:

* the honest evidence passes the deployed gate, so only the pause blocks the leg;
* no obligation of the flow carries a `CommittedRefundBreak`;
* the honest proof of the committed leaf is timeout evidence with no `AbsenceBreak` that does
  not pass the timeout gate;
* unpausing the destination vault and executing the leg on that evidence is a run. -/
def Properties.PausedDestinationStuckWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (prof : Profile)
      (Y : PState) (tr : List Action) (F : Flow) (leg : FlowLeg) (ev : GateEvidence)
      (N : ℕ) (q : ImtProof),
      Wf S ∧ DataAvailable h z0 hl S A ∧ CommittedOnTime cv S F ∧ FlowIdChecked fh F
        ∧ leg ∈ F.legs ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩ Y tr
        ∧ prof.mintsViaVault leg.bundleHash = true
        ∧ Y.flags (prof.dest leg.bundleHash) .vault = true
        ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ (∀ l ∈ F.legs, A l.chain (ev l).1 (ev l).2)
        ∧ authCalls (checkedCalls tr) ≠ []
        ∧ (∀ other ∈ F.legs, ¬ CommittedRefundBreak h z0 hl fh S F (obligationOf F other)
            (authCalls (checkedCalls tr)))
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N q
        ∧ ¬ LegRefundableBy h z0 hl cv S F leg N q
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩
            (Y.setFlag (prof.dest leg.bundleHash) .vault false)
            (Action.execute ⟨F, ev, leg⟩ :: Action.unpause (prof.dest leg.bundleHash) .vault :: tr)

/-- **HEADLINE 4, ON ONE STATE.**  For every node hash, leaf hash and padding constant, inside
the run of `Properties.PauseRunWitness`: the state after both pauses satisfies every premise of
`Properties.PausedVaultKeepsLegRevertable` for the leg `⟨1, 2, 1⟩`.  It is `Revertable`, its
bundle has a router call, and its source vault is paused.  A further run from that state
contains no `unpause` of that vault and executes a leg elsewhere, and the leg is still
`Revertable` at its end.  Unpausing the vault and claiming the leg is a run that leaves it
`Reverted`. -/
def Properties.PausedVaultClaimWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (prof : Profile)
      (X Y : PState) (tr tr₁ : List Action) (c : Chain) (f b : UInt256),
      PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩ X tr
        ∧ prof.recoversViaVault b = true ∧ X.flags c .vault = true
        ∧ stateOf X.mgrs ⟨f, b, c⟩ = .Revertable
        ∧ PRun h z0 hl cv fh S prof X Y tr₁ ∧ Action.unpause c .vault ∉ tr₁
        ∧ (∃ e, Action.execute e ∈ tr₁) ∧ stateOf Y.mgrs ⟨f, b, c⟩ = .Revertable
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩
            ((Y.setFlag c .vault false).setLeg c f b .Reverted)
            (Action.claim c f b :: Action.unpause c .vault :: (tr₁ ++ tr))
        ∧ stateOf ((Y.setFlag c .vault false).setLeg c f b .Reverted).mgrs ⟨f, b, c⟩ = .Reverted

/-- **A DELIVERED LEG AND A STRANDED SIBLING.**  For every node hash, leaf hash and padding
constant, take `pairSystem 1 2`, in which chains `0` and `1` both commit their legs at batch `0`.
Take the commit value `fun _ b => b`, `lengthFlowHash`, and the two-leg flow `mixedFlow 1 1 2`,
which is committed in time and checked.  The profile sends bundle `2` to chain `6` and every
other bundle to chain `5`, all minting through the vault.  The run pauses chain `6`'s vault, then
executes leg `⟨0, 1⟩` on chain `5`.

For leg `⟨1, 2⟩`, every premise of `Properties.PermanentDestinationPauseStrandsLeg` holds, with a
continuation that executes the other leg of the same flow, and no obligation of the flow is
refunded.  Unpausing chain `6`'s vault and executing leg `⟨1, 2⟩` is a run, so the pause alone
strands it. -/
def Properties.DestinationPauseStrandsSiblingWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (prof : Profile) (F : Flow)
      (legA legB : FlowLeg) (evA evB : GateEvidence) (X Y : PState) (tr₀ tr : List Action),
      Wf S ∧ CommittedOnTime cv S F ∧ FlowIdChecked fh F ∧ legA ∈ F.legs ∧ legB ∈ F.legs
        ∧ legA ≠ legB
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩ X tr₀
        ∧ prof.mintsViaVault legB.bundleHash = true
        ∧ X.flags (prof.dest legB.bundleHash) .vault = true
        ∧ PRun h z0 hl cv fh S prof X Y tr
        ∧ Action.unpause (prof.dest legB.bundleHash) .vault ∉ tr
        ∧ Action.execute ⟨F, evA, legA⟩ ∈ tr
        ∧ (∀ other ∈ F.legs, ¬ Refunded Y.mgrs (obligationOf F other))
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩
            (Y.setFlag (prof.dest legB.bundleHash) .vault false)
            (Action.execute ⟨F, evB, legB⟩ :: Action.unpause (prof.dest legB.bundleHash) .vault
              :: (tr ++ tr₀))

/-- **A RUN FROM A PAUSED CENTER.**  For every node hash, leaf hash and padding constant, take
`mixedSystem 1` with `vaultProfile`.  From fresh managers with chain `3`'s `InteropCenter` paused,
a run with no `unpause` appends a leg on chain `1`, so the conclusion of
`Properties.PausedCenterStaysPausedAlongRuns` is about a run that does send, elsewhere.  The send
gate is closed on chain `3` and open on chain `1`. -/
def Properties.PausedCenterWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (prof : Profile) (X Y : PState)
      (tr : List Action) (c c' : Chain) (f b : UInt256),
      PRun h z0 hl cv fh S prof X Y tr ∧ X.flags c .center = true
        ∧ Action.unpause c .center ∉ tr ∧ Action.append c' f b ∈ tr
        ∧ ¬ SendOpen prof X.flags c b ∧ SendOpen prof X.flags c' b

/-- **THE TREE-ATTACHED RESULTS' PREMISES HOLD ON A PAUSED RUN.**  For every node hash, padding
constant and leaf hash: `Contracts.AppendPath`'s system witness, followed by a pause, is a paused
tree-attached run from genesis.  Both logs are nonempty and a flag is still set at its end.  The
executed obligation is not refunded and carries no `RefundBreak`. -/
def Properties.PausedSystemWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (prof : Profile) (F : Flow)
      (ev : GateEvidence) (leg : FlowLeg) (Y : PSysState) (log : List Obligation)
      (alog : List AuthCall),
      Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ PSysSteps h z0 hl cv fh S prof ⟨Contracts.AppendPath.genesisAll, noFlags⟩ Y log alog
        ∧ (∃ c k, Y.flags c k = true) ∧ log ≠ [] ∧ alog ≠ []
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog
        ∧ ¬ Refunded (Contracts.AppendPath.Chains.mgrs Y.chains) (obligationOf F leg)

/-- **THE CALL-LEVEL RESULT'S PREMISES HOLD ON A PAUSED RUN.**  With the extraction-pin padding
`z0 = hl ⟨0,0,0⟩`, in `paddedSystem a b`: `Contracts.FlowBinding`'s padding run, followed by a
pause and an unpause, is a paused run with a logged execution and a logged refund of one flow.
The absence break holds and the inclusion break and the clash fail, so
`Properties.LoggedExecutionExcludesLoggedRefundOrBreakUnderPause` is not vacuous and its break is
located. -/
def Properties.LoggedExecutionExcludesLoggedRefundOrBreakUnderPauseWitness : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    ∃ (cv : CommitValue) (fh : FlowHash) (prof : Profile) (Y : PState) (tr : List Action)
      (e : ExecCall) (r : AuthCall),
      Wf (paddedSystem a b)
        ∧ PRun h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) prof ⟨emptyManagers, noFlags⟩ Y tr
        ∧ (∃ c k, Action.pause c k ∈ tr) ∧ (∃ c k, Action.unpause c k ∈ tr)
        ∧ Action.execute e ∈ tr ∧ Action.authorize r ∈ tr ∧ r.flow.flowId = e.flow.flowId
        ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) r.missing.chain
            (e.evidence r.missing).1 (e.evidence r.missing).2
        ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) r.flow.deadline r.missing.chain
            r.batch r.proof
        ∧ ¬ FlowIdClash fh e.flow r.flow

end Contracts.InteropPause
