import EraSpec.Examples.BurnMintBridge.Model
import EraSpec.Protocol.NoTheft

/-!
# Prepared applications composed with multi-chain commitment histories

Execution evidence covers ALL prerequisites of a flow; recovery evidence names
ONE missing prerequisite. Every prerequisite fixes its own source chain, key,
and deadline, and both evidence types use that exact binding. The missing leg
can differ from the source obligation being recovered.

This composes the existing time-pinned IMT theorem with the new application
model. The family of source histories need not share one root or clock.
`Missing` uses the successor-pinned timeout form. The halted-chain last-batch
branch in `AtomicInteropProof` is not modeled by this adapter yet; its separate
abstract theorems remain in `TimeoutSoundness` and `LastBatchInRoot`.

Still required of a real implementation: authenticated root/leaf proofs, correct
hash binding of the complete flow specification, publication/data availability,
and refinement of every successful execution/refund to these gates and of the
application contract to its preparation laws. Abstract tree membership is called
commitment evidence here; it is not itself application execution.
-/

namespace Properties.PreparedBridge

open IMTAbstract
open Applications

structure Leg where
  sourceChain : UInt256
  commitValue : UInt256
  deadline : UInt256

structure History where
  tree : UInt256 → ℕ → Finset AbsLeaf
  settledAt : UInt256 → ℕ → UInt256

structure History.Valid (H : History) : Prop where
  guarded : ∀ c, GuardedEvolution (H.tree c)
  genesis : ∀ c, H.tree c 0 = ({⟨0, 0⟩} : Finset AbsLeaf)
  monotone_time : ∀ c, Monotone (H.settledAt c)

def OnTime (H : History) (l : Leg) : Prop :=
  ∃ n, H.settledAt l.sourceChain n ≤ l.deadline ∧
    l.commitValue ∈ keys (H.tree l.sourceChain n)

def Missing (H : History) (l : Leg) : Prop :=
  ∃ n W, l.deadline < H.settledAt l.sourceChain (n + 1) ∧
    W ∈ H.tree l.sourceChain n ∧ W.key < l.commitValue ∧
    (W.nextKey = 0 ∨ l.commitValue < W.nextKey)

/-- Time-pinned evidence cannot justify both branches, even when the two
certificates refer to different historical snapshots. -/
theorem onTime_excludes_missing {H : History} (hH : H.Valid) {l : Leg}
    (hon : OnTime H l) : ¬ Missing H l := by
  obtain ⟨n, ht, hkey⟩ := hon
  rintro ⟨j, W, hj, hW, hlow, hwin⟩
  exact (guardedEvolution_delivered_available_forever
    (hH.guarded l.sourceChain) (hH.genesis l.sourceChain)
    (hH.monotone_time l.sourceChain) ht hkey).2 j W hj hW hlow hwin

/-- The flow specification must be bound to the prepared input by the concrete
encoding/hash proof. It is fixed here, not chosen separately by each prover. -/
def evidence (H : History) (flow : BurnMintBridge.Transfer → List Leg) : BurnMintBridge.Evidence where
  finalize := fun i => ∀ l ∈ flow i, OnTime H l
  recover := fun i => ∃ l ∈ flow i, Missing H l

/-- All prerequisites present versus any prerequisite missing is an exclusive
decision across every source chain and every pair of proof snapshots. -/
theorem evidence_sound {H : History} (hH : H.Valid)
    (flow : BurnMintBridge.Transfer → List Leg) : (evidence H flow).Sound := by
  intro i
  rintro ⟨hall, l, hl, hmissing⟩
  exact onTime_excludes_missing hH (hall l hl) hmissing

/-- A prepared reference bridge cannot both mint and recover when driven by
the time-pinned, correctly source-bound evidence of valid chain histories. -/
theorem prepared_bridge_no_double_payment {H : History} (hH : H.Valid)
    (flow : BurnMintBridge.Transfer → List Leg)
    {source destination : ℕ} {s : BurnMintBridge.State}
    (hrun : BurnMintBridge.Run (evidence H flow) (BurnMintBridge.initial source destination) s) :
    ¬ (s.delivered = true ∧ s.refunded = true) :=
  BurnMintBridge.reachable_resolution_exclusive (evidence_sound hH flow) hrun

theorem prepared_bridge_value_conserved {H : History} (hH : H.Valid)
    (flow : BurnMintBridge.Transfer → List Leg)
    {source destination : ℕ} {s : BurnMintBridge.State}
    (hrun : BurnMintBridge.Run (evidence H flow) (BurnMintBridge.initial source destination) s) :
    BurnMintBridge.accounted s = source + destination :=
  BurnMintBridge.reachable_value_conserved (evidence_sound hH flow) hrun

/-- Acceptance of execution evidence anywhere preserves commitment membership
on every prerequisite's source chain at every later snapshot. No single global
snapshot or clock is assumed. This is evidence persistence, not availability. -/
theorem accepted_flow_evidence_persists {H : History} (hH : H.Valid)
    {flow : BurnMintBridge.Transfer → List Leg} {i : BurnMintBridge.Transfer}
    (haccepted : (evidence H flow).finalize i) :
    ∀ l ∈ flow i, ∃ n, H.settledAt l.sourceChain n ≤ l.deadline ∧
      ∀ m, n ≤ m → l.commitValue ∈ keys (H.tree l.sourceChain m) := by
  intro l hl
  obtain ⟨n, ht, hk⟩ := haccepted l hl
  refine ⟨n, ht, ?_⟩
  exact (guardedEvolution_delivered_available_forever
    (hH.guarded l.sourceChain) (hH.genesis l.sourceChain)
    (hH.monotone_time l.sourceChain) ht hk).1

/-- Application execution on one destination carries complete flow evidence.
For every other prepared, still-pending application, that same evidence and its
preparation laws give an enabled execution with its committed effect.

The reference flow uses one fixed specification `legs` on all destinations.
The equality hypotheses are intentional: binding each local input to that same
specification is a concrete implementation obligation, not an inference from
the existence of arbitrary commitments. -/
theorem execution_enables_other_prepared_legs
    {Destination : Type*} {H : History}
    (flow : BurnMintBridge.Transfer → List Leg) (legs : List Leg)
    {executedInput effect : BurnMintBridge.Transfer} {executedBefore executedAfter : BurnMintBridge.State}
    (hfirst : BurnMintBridge.AuthorizedExecution (evidence H flow)
      executedBefore executedInput effect executedAfter)
    (hsame : flow executedInput = legs)
    (inputs : Destination → BurnMintBridge.Transfer)
    (before prepared current : Destination → BurnMintBridge.State)
    (hbound : ∀ d, flow (inputs d) = legs)
    (hprepare : ∀ d, BurnMintBridge.Prepare (before d) (inputs d) (prepared d))
    (hwait : ∀ d, Prepared.InterferenceRun BurnMintBridge.application (prepared d) (current d)) :
    ∀ d, (evidence H flow).finalize (inputs d) ∧
      ∃ after, BurnMintBridge.Execute (current d) (inputs d) (inputs d) after := by
  intro d
  refine ⟨?_, BurnMintBridge.prepared_mint_survives_spending (hprepare d) (hwait d)⟩
  change ∀ l ∈ flow (inputs d), OnTime H l
  rw [hbound d, ← hsame]
  exact hfirst.1

end Properties.PreparedBridge
