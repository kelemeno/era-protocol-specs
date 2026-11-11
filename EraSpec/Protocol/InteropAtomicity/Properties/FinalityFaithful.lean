import EraSpec.Protocol.InteropAtomicity.Specs.FinalityFaithful

/-!
# Properties: finalizability at a destination that has to authenticate the roots

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.FinalityFaithful`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.FinalityFaithful`.

## What this corrects

The positive disjunct of `Contracts.Atomicity.Properties.NoneOrAll(OrBreak/Pinned)`,
`ExecutedImpliesAllFinalizable(OrBreak)` and `ExecutedImpliesFinalityPersists(OrBreak)` is
`FlowFinalizableBy`, which has no destination in it.  Read as "every leg's destination can
run `requireFlowFinalized` and pass", it is false without an assumption about root import:
`Properties.ExecutedFlowNotFinalizableAtUnimportedDestination` has a two-leg flow executed
at one destination, with data available and `FlowFinalizableBy` true, while the destination
of the other leg, which has imported no settlement-layer root, can finalize neither leg.

## What replaces it

With the explicit root-availability premise `PostDeadlineRootAt` (the destination has
imported one honest settlement-layer root created at or after the deadline), the
destination-level statements hold, with no hash premise and the same located break as the
`…OrBreak` forms:

* `Properties.ExecutedImpliesFinalizableAtImportingDestinationOrBreak`;
* `Properties.NoneOrAllAtImportingDestinationOrBreak`;
* `Properties.ExecutedFinalityPersistsAtAuthenticatingDestinationOrBreak`, which needs only
  that the destination can authenticate the later batch.

`Properties.FinalizableAtImportingDestinationWitness` meets every premise together with an
executed flow, no gate break, and a finalizable flow at that destination.
-/

namespace Contracts.FinalityFaithful

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout

/-! ## The countermodel -/

/-- **AN EXECUTED FLOW IS NOT FINALIZABLE AT A DESTINATION WITHOUT AN IMPORTED ROOT.**  For
every node hash, leaf hash and padding constant: in `everyChainSystem 1 2` (every chain holds
the values `1` and `2` from batch 0), `twoChainFlow` executes at destination `5` on honest
evidence, with data available (honest access) and with `5` authenticating every root its gate
checked.  `FlowFinalizableBy`, the conclusion of `ExecutedImpliesAllFinalizable`, holds.  Yet
at destination `6`, the destination of the sibling leg `⟨1, 2⟩`, which has imported no root,
that leg is not finalizable, and the root-availability premise fails there. -/
def Properties.ExecutedFlowNotFinalizableAtUnimportedDestination : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (A : Access) (ev : GateEvidence),
      Wf (everyChainSystem 1 2)
        ∧ DataAvailable h z0 hl (everyChainSystem 1 2) A
        ∧ ExecutedAtBy h z0 hl (fun _ bh => bh) (honestFlowHash twoChainFlow)
            (everyChainSystem 1 2) importsAtFive 5 twoChainFlow ev ⟨0, 1⟩
        ∧ FlowFinalizableBy h z0 hl (fun _ bh => bh) (everyChainSystem 1 2) A twoChainFlow
        ∧ ¬ LegFinalizableAt h z0 hl (fun _ bh => bh) (everyChainSystem 1 2) A importsAtFive 6
            twoChainFlow ⟨1, 2⟩
        ∧ ¬ FlowFinalizableAt h z0 hl (fun _ bh => bh) (everyChainSystem 1 2) A importsAtFive 6
            twoChainFlow
        ∧ ¬ PostDeadlineRootAt (everyChainSystem 1 2) importsAtFive 6 twoChainFlow.deadline

/-! ## The replacements -/

/-- **ONE EXECUTION MAKES EVERY LEG FINALIZABLE AT EVERY DESTINATION THAT HAS IMPORTED A
POST-DEADLINE ROOT, OR A LOCATED BREAK.**  `Contracts.Atomicity.Properties.
ExecutedImpliesAllFinalizableOrBreak` at a named destination `d`, with the root-availability
premise `PostDeadlineRootAt S I d F.deadline` next to `DataAvailable`. -/
def Properties.ExecutedImpliesFinalizableAtImportingDestinationOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (I : Imports) (d : Chain) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
      ExecutedViaBy h z0 hl cv fh S F ev leg → PostDeadlineRootAt S I d F.deadline →
      ∀ other ∈ F.legs,
        LegFinalizableAt h z0 hl cv S A I d F other
          ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-- **NONE OR ALL, AT A DESTINATION THAT HAS IMPORTED A POST-DEADLINE ROOT.**  For every flow
and gate evidence: the whole gate can pass at `d`, or no leg executes on that evidence, or the
evidence carries a located break. -/
def Properties.NoneOrAllAtImportingDestinationOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (I : Imports) (d : Chain) (F : Flow) (ev : GateEvidence),
      PostDeadlineRootAt S I d F.deadline →
        FlowFinalizableAt h z0 hl cv S A I d F
          ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
          ∨ GateBreak h z0 hl S F ev

/-- **FINALIZABILITY PERSISTS, AT A DESTINATION THAT CAN AUTHENTICATE A LATER ON-TIME BATCH.**
The faithful form of `Contracts.Atomicity.Properties.ExecutedImpliesFinalityPersistsOrBreak`:
a destination that holds a root aggregating ANY on-time batch at or after the one the
execution used can finalize the leg.  "Imports a later root" is a premise here, not a
reading of the conclusion, and the premise is weaker than `PostDeadlineRootAt`: no honest
aggregation is assumed, only that this one batch is in a root the destination holds. -/
def Properties.ExecutedFinalityPersistsAtAuthenticatingDestinationOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (I : Imports) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
      ExecutedViaBy h z0 hl cv fh S F ev leg →
      ∀ other ∈ F.legs,
        (∀ (d : Chain) (m : ℕ), (ev other).1 ≤ m → S.time other.chain m ≤ F.deadline →
            CanAuthenticate I d other.chain m → LegFinalizableAt h z0 hl cv S A I d F other)
          ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-! ## Anti-vacuity -/

/-- **THE PREMISES HOLD TOGETHER, AND THE CONCLUSION IS REACHED WITH NO BREAK.**  For every node
hash, leaf hash and padding constant: in `everyChainSystem 1 2`, `twoChainFlow` executes on
honest evidence with honest access (data available); destination `5` has imported
`timeOneRoot`, which was created after the deadline and aggregates honestly; the gate evidence
carries no break; and the flow is finalizable at `5`. -/
def Properties.FinalizableAtImportingDestinationWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (A : Access) (ev : GateEvidence),
      Wf (everyChainSystem 1 2) ∧ DataAvailable h z0 hl (everyChainSystem 1 2) A
        ∧ ExecutedViaBy h z0 hl (fun _ bh => bh) (honestFlowHash twoChainFlow)
            (everyChainSystem 1 2) twoChainFlow ev ⟨0, 1⟩
        ∧ PostDeadlineRootAt (everyChainSystem 1 2) importsAtFive 5 twoChainFlow.deadline
        ∧ ¬ GateBreak h z0 hl (everyChainSystem 1 2) twoChainFlow ev
        ∧ FlowFinalizableAt h z0 hl (fun _ bh => bh) (everyChainSystem 1 2) A importsAtFive 5
            twoChainFlow

end Contracts.FinalityFaithful
