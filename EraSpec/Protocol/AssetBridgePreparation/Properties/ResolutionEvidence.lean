import EraSpec.Protocol.AssetBridgePreparation.Specs.ResolutionEvidence

/-!
# Properties: the two-chain trace driven by the protocol's own evidence

Statements about `EraSpec.Protocol.AssetBridgePreparation.Specs.ResolutionEvidence`; proofs are
in `EraSpec.Protocol.AssetBridgePreparation.Proofs.ResolutionEvidence`. No statement takes a hash
premise: every node hash, leaf hash, padding constant, commit value and flow hash is universally
quantified, and the breaks are located on named submitted proofs.

## Atomic interop

* `InteropGateSoundOrBreak`: on a well-formed history the atomic interop gate is sound up to
  `RefundBreak`, located on the two witnesses.
* `InteropTwoChainConservedOrBreak` (headline): the two-chain books balance, or the run delivered
  some entry through the deployed gate on evidence `ev` and refunded it through a logged manager
  run whose log carries a `RefundBreak` against `ev`.
* `InteropTwoChainResolvesOnceOrBreak`: each entry is resolved at most once, or the same located
  break.

## Multichain refund gate

* `MultichainGateSound`: with every chain's tree valid, the bound gate is sound outright.
* `MultichainTwoChainConserved`: the books balance and each entry is resolved at most once.
* `MultichainUnboundGateDoublePays` (countermodel): without the source-chain check, a bridge run
  over valid trees delivers and refunds the same entry and the books end its amount too high.

## Anti-vacuity

* `InteropTwoChainSatisfiable`: on `mixedSystem 1` (well formed), one entry is delivered through
  the deployed gate on honest proofs and another is refunded through a nonempty logged manager
  run; the books balance and the break predicate is false on the delivered entry's evidence
  against that log.
* `InteropTwoChainPaddingDoublePayLocated`: the break fires where the bug is. With the forged
  padding absence proof of `paddedSystem`, the bridge pays one entry twice, and the located break
  is exactly the forged absence proof.
* `MultichainTwoChainSatisfiable`: over the valid trees of `attackChains v`, one entry is
  delivered and another refunded under the bound gate.
-/

namespace AssetBridgePreparation

open Contracts MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Refund

/-! ## Atomic interop -/

/-- **THE ATOMIC INTEROP GATE IS SOUND UP TO A LOCATED BREAK.** On a well-formed history, if entry
`i`'s leg executed through the deployed gate on evidence `ev`, and a logged manager run
`(Ms, log)` from fresh storage lifted its obligation past `Committed`, then `log` contains a call
that marked that obligation and carries a `RefundBreak` against `ev`. No hash premise. -/
def Properties.InteropGateSoundOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (route : ResolutionLegRoute),
    Wf S →
      (interopResolutionGate h z0 hl cv fh S route).SoundOrBreak
        (interopResolutionBreak h z0 hl fh S route)

/-- **CONSERVATION ACROSS BOTH CHAINS UNDER THE DEPLOYED GATE, OR A LOCATED BREAK.** With the
atomic interop evidence on a well-formed history, along every run from a `WellFormed` source
whose records start empty: the source supply plus the destination supply plus the value in
flight is constant, or the run's labels deliver some entry `i` on gate evidence `ev` with which
its leg executed through the deployed gate, and refund it on a logged manager run `(Ms, log)` from
fresh storage, and `log` carries a `RefundBreak` for that leg's obligation against `ev`. -/
def Properties.InteropTwoChainConservedOrBreak : Prop :=
  ∀ (A B : Type) (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (route : ResolutionLegRoute)
    (E : TwoChainEnv A B GateEvidence InteropRefundWitness) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel GateEvidence InteropRefundWitness)),
    E.gate = interopResolutionGate h z0 hl cv fh S route → Wf S →
    NativeTokenVaultBase.WellFormed s.source → s.FreshRecords → TwoChainRun E s ls t →
      t.circulating + t.outstanding = s.circulating + s.outstanding ∨
        ∃ (i : ℕ) (ev : GateEvidence) (Ms : Managers) (log : List AuthCall),
          TwoChainLabel.deliver i ev ∈ ls ∧ TwoChainLabel.refund i (Ms, log) ∈ ls ∧
          ExecutedViaBy h z0 hl cv fh S (route i).1 ev (route i).2 ∧
          ReachLog h z0 hl cv fh S emptyManagers Ms log ∧
          RefundBreak h z0 hl fh S (route i).1 ev (obligationOf (route i).1 (route i).2) log

/-- **EACH ENTRY RESOLVED AT MOST ONCE UNDER THE DEPLOYED GATE, OR A LOCATED BREAK.** -/
def Properties.InteropTwoChainResolvesOnceOrBreak : Prop :=
  ∀ (A B : Type) (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (route : ResolutionLegRoute)
    (E : TwoChainEnv A B GateEvidence InteropRefundWitness) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel GateEvidence InteropRefundWitness)),
    E.gate = interopResolutionGate h z0 hl cv fh S route → Wf S → s.FreshRecords →
    TwoChainRun E s ls t →
    ∀ i : ℕ,
      deliveryCount ls i + refundCount ls i ≤ 1 ∨
        ∃ (ev : GateEvidence) (Ms : Managers) (log : List AuthCall),
          TwoChainLabel.deliver i ev ∈ ls ∧ TwoChainLabel.refund i (Ms, log) ∈ ls ∧
          RefundBreak h z0 hl fh S (route i).1 ev (obligationOf (route i).1 (route i).2) log

/-- **THE INTEROP PREMISES HOLD WITH BOTH RESOLUTIONS FIRING, AND THE BREAK IS NOT A
TAUTOLOGY.** For every node hash, leaf hash and padding constant: on the well-formed
`mixedSystem 1`, entry `0` is carried by the one-leg flow `subsetFlow 0 1`, which executes through
the deployed gate on the honest inclusion proof; entry `1` by a leg of the checked flow
`mixedFlow 1 1 2`, whose obligation a logged manager run (one `authorizeRefund` on an honest
absence proof) lifts to `Revertable`. The two-chain run from a fresh trace prepares both, delivers
entry `0` on that gate evidence and refunds entry `1` on that manager run. The books balance, and
the break predicate is false for the delivered entry's evidence against the (nonempty) refund
log. -/
def Properties.InteropTwoChainSatisfiable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (route : ResolutionLegRoute)
      (E : TwoChainEnv Unit Unit GateEvidence InteropRefundWitness)
      (s t : TwoChainLedger Unit Unit)
      (ls : List (TwoChainLabel GateEvidence InteropRefundWitness))
      (ev : GateEvidence) (Ms : Managers) (log : List AuthCall),
      E.gate = interopResolutionGate h z0 hl cv fh S route ∧ Wf S ∧
      NativeTokenVaultBase.WellFormed s.source ∧ s.FreshTrace ∧ TwoChainRun E s ls t ∧
      TwoChainLabel.deliver 0 ev ∈ ls ∧ TwoChainLabel.refund 1 (Ms, log) ∈ ls ∧ log ≠ [] ∧
      0 ∈ t.delivered ∧ 1 ∈ t.refunded ∧
      ¬ interopResolutionBreak h z0 hl fh S route 0 ev (Ms, log) ∧
      t.circulating + t.outstanding = s.circulating + s.outstanding

/-- **THE BREAK FIRES WHERE THE BUG IS, AT THE BRIDGE.** With the extraction-pin padding
`z0 = hl ⟨0, 0, 0⟩`, on the well-formed `paddedSystem a b`: a one-leg flow executes on the honest
inclusion proof, and a logged manager run authorizes its refund on the forged padding absence
proof. The two-chain run from a fresh trace prepares one entry carried by that leg, delivers it on
the gate evidence and refunds it on the manager run. The entry is paid twice and the books end
its (nonzero) amount above their start. The located break holds, and it is exactly the forged
absence proof: every logged call is the executed flow's own, with no flow-id collision and no
break on the executed flow's inclusion proof, and its absence proof carries an `AbsenceBreak`. -/
def Properties.InteropTwoChainPaddingDoublePayLocated : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    ∃ (cv : CommitValue) (fh : FlowHash) (route : ResolutionLegRoute)
      (E : TwoChainEnv Unit Unit GateEvidence InteropRefundWitness)
      (s t : TwoChainLedger Unit Unit)
      (ls : List (TwoChainLabel GateEvidence InteropRefundWitness))
      (ev : GateEvidence) (Ms : Managers) (log : List AuthCall),
      E.gate = interopResolutionGate h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) route ∧
      Wf (paddedSystem a b) ∧ NativeTokenVaultBase.WellFormed s.source ∧ s.FreshTrace ∧
      TwoChainRun E s ls t ∧
      TwoChainLabel.deliver 0 ev ∈ ls ∧ TwoChainLabel.refund 0 (Ms, log) ∈ ls ∧
      0 ∈ t.delivered ∧ 0 ∈ t.refunded ∧ pendingAmountAt t.pending 0 ≠ 0 ∧
      t.circulating + t.outstanding =
        s.circulating + s.outstanding + pendingAmountAt t.pending 0 ∧
      interopResolutionBreak h (hl ⟨0, 0, 0⟩) hl fh (paddedSystem a b) route 0 ev (Ms, log) ∧
      ∀ c ∈ log, c.flow = (route 0).1 ∧ ¬ FlowIdClash fh (route 0).1 c.flow ∧
        ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) c.missing.chain
            (ev c.missing).1 (ev c.missing).2 ∧
        AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) (route 0).1.deadline
          c.missing.chain c.batch c.proof

/-! ## Multichain refund gate -/

/-- **THE BOUND MULTICHAIN GATE IS SOUND.** If every chain's commitment-tree contract state is
valid, no entry has both a delivered commit value and an absence witness on its declared source
chain. -/
def Properties.MultichainGateSound : Prop :=
  ∀ (T : UInt256 → Tree) (route : ResolutionValueRoute),
    (∀ c, Valid (T c)) → (multichainResolutionGate T route).Sound

/-- **CONSERVATION UNDER THE BOUND MULTICHAIN GATE.** With every chain's tree valid, along every
run from a `WellFormed` source whose records start empty, the books balance and each entry is
resolved at most once. -/
def Properties.MultichainTwoChainConserved : Prop :=
  ∀ (A B : Type) (T : UInt256 → Tree) (route : ResolutionValueRoute)
    (E : TwoChainEnv A B Unit Unit) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Unit Unit)),
    E.gate = multichainResolutionGate T route → (∀ c, Valid (T c)) →
    NativeTokenVaultBase.WellFormed s.source → s.FreshRecords → TwoChainRun E s ls t →
      t.circulating + t.outstanding = s.circulating + s.outstanding ∧
        ∀ i : ℕ, deliveryCount ls i + refundCount ls i ≤ 1

/-- **THE BOUND-GATE PREMISES ARE SATISFIABLE WITH BOTH RESOLUTIONS FIRING.** For every nonzero
`v`, over the valid trees of `attackChains v` (chain `0` has inserted `v`, every other chain is
at genesis), entry `0` (commit value `v` on chain `0`) is delivered and entry `1` (commit value
`v` on chain `1`) is refunded, in one run from a fresh trace. -/
def Properties.MultichainTwoChainSatisfiable : Prop :=
  ∀ v : UInt256, 0 < v →
    ∃ (route : ResolutionValueRoute) (E : TwoChainEnv Unit Unit Unit Unit)
      (s t : TwoChainLedger Unit Unit) (ls : List (TwoChainLabel Unit Unit)),
      E.gate = multichainResolutionGate (Contracts.Protocol.attackChains v) route ∧
      (∀ c, Valid (Contracts.Protocol.attackChains v c)) ∧
      NativeTokenVaultBase.WellFormed s.source ∧ s.FreshTrace ∧ TwoChainRun E s ls t ∧
      0 ∈ t.delivered ∧ 1 ∈ t.refunded

/-- **COUNTERMODEL: WITHOUT THE SOURCE-CHAIN CHECK THE BRIDGE PAYS TWICE.** For every nonzero `v`,
over the valid trees of `attackChains v`, with the gate that accepts an absence witness from any
chain: one entry whose commit value `v` is delivered on its declared source chain `0` is
delivered at the destination and refunded at the source (on chain `1`'s truthful absence
witness), and the books end its nonzero amount above their start. -/
def Properties.MultichainUnboundGateDoublePays : Prop :=
  ∀ v : UInt256, 0 < v →
    ∃ (E : TwoChainEnv Unit Unit Unit Unit) (s t : TwoChainLedger Unit Unit)
      (ls : List (TwoChainLabel Unit Unit)),
      E.gate =
        unboundMultichainResolutionGate (Contracts.Protocol.attackChains v) (fun _ => (0, v)) ∧
      (∀ c, Valid (Contracts.Protocol.attackChains v c)) ∧
      NativeTokenVaultBase.WellFormed s.source ∧ s.FreshTrace ∧ TwoChainRun E s ls t ∧
      0 ∈ t.delivered ∧ 0 ∈ t.refunded ∧ pendingAmountAt t.pending 0 ≠ 0 ∧
      t.circulating + t.outstanding =
        s.circulating + s.outstanding + pendingAmountAt t.pending 0

end AssetBridgePreparation
