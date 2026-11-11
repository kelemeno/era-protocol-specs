import EraSpec.Protocol.FlowAtomicity

/-!
# Flow atomicity with one commitment history per source chain

`EraSpec.Protocol.FlowAtomicity` states its results over ONE history `S` for all legs of a
flow, and its header presents that as the protocol: "the interop roots are published to every
chain, so every chain of the flow verifies its legs against snapshots of the same evolving key
set".  The source does not work that way.  `AtomicFlowManager.append` inserts a leg's commit
value into the SENDING chain's `L2InteropCommitmentTree`
(`atomic-interop/AtomicFlowManager.sol:40`, `:97-99`, pin `c67894b9`), and
`requireFlowFinalized` checks each leg against its DECLARED source chain's tree
(`:122-129`; `libraries/AtomicInteropProof.sol:30-31`).  The imported settlement-layer root
is common to all chains; the key sets are per chain.  `InteropAtomicity`'s `System.tree` is
already indexed that way.

This file restates the `FlowAtomicity` results over a history per chain, so that they apply
to multi-chain flows, and shows the shared-history premise cannot describe a two-chain flow
whose chains committed different legs.  It does not add a claim that no leg is ever stuck:
the per-leg dichotomy is a fact about one chain's leaf set, and whether a prover can
authenticate that tree for the leg's declared chain is a separate question (data
availability, `Contracts.Atomicity.Properties.WithoutDaCommittedLegIsStuck`; root import,
`Contracts.FinalityFaithful.Properties.ExecutedFlowNotFinalizableAtUnimportedDestination`).

Pure order theory over `IMTAbstract`, as `FlowAtomicity` is.
-/

namespace AttackVectors.FlowAtomicityPerChain

open IMTAbstract

/-- A leg of a multi-chain flow: its declared source chain and its commit value. -/
structure ChainLeg where
  chain : UInt256
  value : UInt256

/-- **LEG EVIDENCE NEVER DECAYS, ON THE LEG'S OWN CHAIN.**  If every chain's history is an
`Evolution` and leg `leg` is delivered at snapshot `i` of its own chain, it is delivered at
every later snapshot of that chain. -/
theorem leg_evidence_never_decays_per_chain {S : UInt256 → ℕ → Finset AbsLeaf}
    (hevo : ∀ c, Evolution (S c)) (flow : List ChainLeg) {leg : ChainLeg} (_hleg : leg ∈ flow)
    {i : ℕ} (hdel : leg.value ∈ keys (S leg.chain i)) :
    ∀ j, i ≤ j → leg.value ∈ keys (S leg.chain j) :=
  fun _ hij => evolution_keys_mono (hevo leg.chain) hij hdel

/-- **EXECUTED ON ITS CHAIN ⟹ PRESENT AT EVERY LATER ROOT OF THAT CHAIN, FOR EVERY LEG.**  The
multi-chain form of `FlowAtomicity.executed_leg_executable_at_every_later_root`: snapshot
indices are per chain (`n c`), since different chains' batches are not aligned.  If every leg
is delivered at its own chain's snapshot `n leg.chain`, every leg is present at every later
snapshot of its own chain. -/
theorem executed_legs_present_at_every_later_root_per_chain {S : UInt256 → ℕ → Finset AbsLeaf}
    (hevo : ∀ c, Evolution (S c)) (flow : List ChainLeg) {n : UInt256 → ℕ}
    (hall : ∀ leg ∈ flow, leg.value ∈ keys (S leg.chain (n leg.chain))) :
    ∀ leg ∈ flow, ∀ j, n leg.chain ≤ j → leg.value ∈ keys (S leg.chain j) :=
  fun leg hleg _ hj => evolution_keys_mono (hevo leg.chain) hj (hall leg hleg)

/-- **ONE OUTCOME PER LEG, AGAINST THE LEG'S OWN CHAIN'S TREE.**  The multi-chain form of
`FlowAtomicity.flow_outcome_dichotomy`: along guarded histories from genesis, every nonzero
leg, at every snapshot `j leg.chain` of its own chain, is delivered there or has a reclaim
witness there, and never both.  This is a statement about leaf sets; it says nothing about
whether a prover can present the witness. -/
theorem flow_outcome_dichotomy_per_chain {S : UInt256 → ℕ → Finset AbsLeaf}
    (hge : ∀ c, GuardedEvolution (S c)) (hgen : ∀ c, S c 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (flow : List ChainLeg) (hnz : ∀ leg ∈ flow, leg.value ≠ 0) (j : UInt256 → ℕ) :
    ∀ leg ∈ flow,
      (leg.value ∈ keys (S leg.chain (j leg.chain))
          ∨ ∃ W ∈ S leg.chain (j leg.chain), W.key < leg.value
              ∧ (W.nextKey = 0 ∨ leg.value < W.nextKey))
        ∧ ¬ (leg.value ∈ keys (S leg.chain (j leg.chain))
          ∧ ∃ W ∈ S leg.chain (j leg.chain), W.key < leg.value
              ∧ (W.nextKey = 0 ∨ leg.value < W.nextKey)) := by
  intro leg hleg
  have hiff := guardedEvolution_reclaimable_iff_absent (hge leg.chain) (hgen leg.chain)
    (j := j leg.chain) (hnz leg hleg)
  constructor
  · by_cases hmem : leg.value ∈ keys (S leg.chain (j leg.chain))
    · exact Or.inl hmem
    · exact Or.inr (hiff.mpr hmem)
  · rintro ⟨hmem, hwit⟩
    exact hiff.mp hwit hmem

/-- **THE SHARED-HISTORY STATEMENT IS THE ONE-CHAIN CASE.**
`FlowAtomicity.executed_leg_executable_at_every_later_root` is
`executed_legs_present_at_every_later_root_per_chain` for a flow whose legs all sit on one
chain `c`, with that chain's history `S₀`. -/
theorem shared_history_is_single_chain_case {S₀ : ℕ → Finset AbsLeaf} (hevo : Evolution S₀)
    (c : UInt256) (flow : List UInt256) {n : ℕ} (hall : ∀ v ∈ flow, v ∈ keys (S₀ n)) :
    ∀ j, n ≤ j → ∀ v ∈ flow, v ∈ keys (S₀ j) := by
  intro j hj v hv
  have := executed_legs_present_at_every_later_root_per_chain (S := fun _ => S₀)
    (fun _ => hevo) (flow.map fun v => ⟨c, v⟩) (n := fun _ => n)
    (fun leg hleg => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hleg
      exact hall w hw)
    ⟨c, v⟩ (List.mem_map.mpr ⟨v, hv, rfl⟩) j hj
  exact this

/-- **A TWO-CHAIN FLOW HAS NO SHARED HISTORY.**  For distinct nonzero commit values `a, b`,
there are guarded per-chain histories from genesis in which leg `(0, a)` is delivered on chain
`0` and leg `(1, b)` on chain `1` at snapshot 1, while `b` is absent from chain `0`'s tree
there.  No single history `S₀` is both chains' history, so the `FlowAtomicity` header's
premise does not describe this flow; and checking leg `b` against chain `0`'s key set would
find it missing, which is the confusion `authorizeRefund`'s source-chain check exists to
prevent (`Contracts.Protocol.Properties.unbound_gate_refunds_delivered_leg`). -/
theorem two_chain_flow_has_no_shared_history {a b : UInt256} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) :
    ∃ S : UInt256 → ℕ → Finset AbsLeaf,
      (∀ c, GuardedEvolution (S c) ∧ S c 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
        ∧ a ∈ keys (S 0 1) ∧ b ∈ keys (S 1 1) ∧ b ∉ keys (S 0 1)
        ∧ ¬ ∃ S₀ : ℕ → Finset AbsLeaf, S 0 = S₀ ∧ S 1 = S₀ := by
  classical
  obtain ⟨S₀, hge₀, hgen₀, _, _, ha₀, hb₀, _⟩ :=
    AttackVectors.FlowAtomicity.mixed_outcomes_permitted ha hb hab
  obtain ⟨S₁, hge₁, hgen₁, _, _, hb₁, _, _⟩ :=
    AttackVectors.FlowAtomicity.mixed_outcomes_permitted hb ha (Ne.symm hab)
  refine ⟨fun c => if c = 0 then S₀ else S₁, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    by_cases hc : c = 0
    · simp only [hc, if_true]
      exact ⟨hge₀, hgen₀⟩
    · simp only [hc, if_false]
      exact ⟨hge₁, hgen₁⟩
  · simpa using ha₀
  · have h10 : (1 : UInt256) ≠ 0 := by decide
    simpa [h10] using hb₁
  · simpa using hb₀
  · rintro ⟨T, h0, h1⟩
    have h10 : (1 : UInt256) ≠ 0 := by decide
    have e0 : S₀ = T := by simpa using h0
    have e1 : S₁ = T := by simpa [h10] using h1
    exact hb₀ (by rw [e0, ← e1]; exact hb₁)

end AttackVectors.FlowAtomicityPerChain
