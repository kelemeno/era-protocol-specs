import EraSpec.Contracts.InteropHandlerBase.History.Properties.BundleStatusMachineFaithful
import EraSpec.Contracts.InteropHandlerBase.History.Proofs.BundleStatusMachine
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineFaithful
import Mathlib.Tactic

/-! **History: a record of the interop pin `c67894b9`, not a claim about era-contracts `b17415d20`.**
The labelled machine `LStep` labels the pin's edges: an inclusion-proof `executeBundle`/`verifyBundle`
on both layers and an `executeAtomicBundle` that admits `Unreceived` only
(pin `L2InteropHandler.sol:79`). At `b17415d20` L2 has no inclusion-proof entry point; its
`verifyAtomicBundle` (`interop/interop-handler/L2InteropHandler.sol:83-92`) is a flow-gated
`Unreceived → Verified` edge `LStep` lacks, and `executeAtomicBundle` (`:61-78`) admits `Verified`
and skips the flow gate for it. The never-published statements rest on the pin's argument that an
atomic bundle never reaches `Verified`, and `VerifiedBundleRunsWithoutAnyGate` on the pin's atomic
entry refusing `Verified`. The `b17415d20` gate results are in topic `Reentrancy`
(`DeliveryNeedsTheGateAtV35`, `VerifiedBundleExecutesWithoutTheGateAtV35`). Namespaces carry a
`History` segment. -/

namespace AttackVectors.BundleStatusMachine.Faithful.History

open AttackVectors.BundleStatusMachine AttackVectors.BundleStatusMachine.History

theorem lstep_refines_step : Properties.lstep_refines_step := by
  intro s t
  constructor
  · intro h
    cases h
    · exact ⟨_, _, .verify⟩
    · exact ⟨_, _, .executeFresh⟩
    · exact ⟨_, _, .executeVerified⟩
    · exact ⟨_, _, .unbundleFirst⟩
    · exact ⟨_, _, .unbundleAgain⟩
    · exact ⟨_, _, .executeAtomic⟩
  · rintro ⟨e, c, h⟩
    cases h
    · exact .verify
    · exact .executeFresh
    · exact .executeVerified
    · exact .unbundleFirst
    · exact .unbundleAgain
    · exact .executeAtomic

theorem atomic_entry_needs_unreceived : Properties.atomic_entry_needs_unreceived := by
  intro s t c h
  cases h
  rfl

theorem verified_runs_unchecked : Properties.verified_runs_unchecked :=
  ⟨.executeVerified, .unbundleFirst⟩

/-- Along a labelled path from `Unreceived`, either the bundle is still `Unreceived`, or an inclusion
proof or the flow gate was consulted. -/
lemma lreach_from_unreceived {a t : Status} {cs : List Check} (h : LReach a cs t) :
    a = .Unreceived → t = .Unreceived ∨ Check.inclusionProof ∈ cs ∨ Check.flowGate ∈ cs := by
  induction h with
  | refl => exact Or.inl
  | tail _ hs ih =>
    intro ha
    rcases ih ha with hb | hin | hin
    · subst hb
      cases hs <;> simp
    · exact Or.inr (Or.inl (List.mem_append_left _ hin))
    · exact Or.inr (Or.inr (List.mem_append_left _ hin))

theorem route_consults_inclusion_or_flowGate :
    Properties.route_consults_inclusion_or_flowGate := by
  intro cs t h ht
  rcases lreach_from_unreceived h rfl with hu | hin
  · subst hu
    rcases ht with h' | h' <;> exact absurd h' (by decide)
  · exact hin

/-- A labelled path from `Unreceived` consulting no inclusion proof stays inside `AtomicReach`. -/
lemma lreach_no_inclusion {a t : Status} {cs : List Check} (h : LReach a cs t) :
    a = .Unreceived → Check.inclusionProof ∉ cs → AtomicReach .Unreceived t := by
  induction h with
  | refl => intro ha _; subst ha; exact .refl _
  | @tail b d cs e c _ hs ih =>
    intro ha hno
    have hno₁ : Check.inclusionProof ∉ cs := fun hm => hno (List.mem_append_left _ hm)
    have hc : c ≠ Check.inclusionProof := fun hc => hno (by simp [hc])
    have hb := ih ha hno₁
    rcases AttackVectors.BundleStatusMachine.History.atomic_reach_two_states hb with hb' | hb'
    · subst hb'
      cases hs with
      | verify => exact absurd rfl hc
      | executeFresh => exact absurd rfl hc
      | executeAtomic => exact .tail hb .executeAtomic
    · subst hb'
      cases hs

theorem no_inclusion_paths_are_atomic : Properties.no_inclusion_paths_are_atomic :=
  fun _ _ h hno => lreach_no_inclusion h rfl hno

theorem inclusion_routes_skip_flowGate : Properties.inclusion_routes_skip_flowGate := by
  have h₁ : LReach .Unreceived ([] ++ [Check.inclusionProof]) .FullyExecuted :=
    .tail (.refl _) .executeFresh
  have h₂ : LReach .Unreceived ([] ++ [Check.inclusionProof] ++ [Check.noCheck]) .FullyExecuted :=
    .tail (.tail (.refl _) .verify) .executeVerified
  have h₃ : LReach .Unreceived ([] ++ [Check.inclusionProof] ++ [Check.noCheck]) .Unbundled :=
    .tail (.tail (.refl _) .verify) .unbundleFirst
  exact ⟨h₁, h₂, h₃⟩

end AttackVectors.BundleStatusMachine.Faithful.History

namespace Contracts.InteropHandler.Faithful.History

open Contracts.InteropHandler Contracts.InteropHandler.Faithful
open AttackVectors.BundleStatusMachine
open AttackVectors.BundleStatusMachine.History

theorem NeverPublishedBundleNeedsTheFlowGate :
    Properties.NeverPublishedBundleNeedsTheFlowGate := by
  intro s h txs hu hno
  refine ⟨?_, fun ⟨e, he, heh⟩ hgate => ?_⟩
  · rcases submitAll_atomicStates h s txs (Or.inl hu) hno with h1 | h1
    · rw [h1]; exact .refl _
    · rw [h1]; exact .tail (.refl _) .executeAtomic
  · exact (submitAll_untouched h s txs hu
      (fun t ht => TxAll.and (hno t ht) (hgate t ht))).2 e he heh

/-! ## The countermodels -/

/-- `executeBundle` with an accepted proof, from `Unreceived`, targets returning. -/
lemma exec_public_fresh {s : State} {b : Bundle} (hu : s.bundle b.hash = .Unreceived) :
    exec .deployed (b.calls + 2) (.entry (.executeBundle b true) (List.replicate b.calls .returns)) s =
      some (beforeCalls .deployed b (s.verifyIfUnreceived b.hash),
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]) := by
  show exec .deployed (b.calls + 1 + 1) _ s = _
  simp only [exec]
  rw [exec_calls_returns .deployed b.hash _ _ _ _ (fun c hc => (List.mem_replicate.1 hc).2)
    (by simp)]
  simp [hu]

/-- `executeBundle` with no accepted proof, from `Verified`, targets returning. -/
lemma exec_public_verified {s : State} {b : Bundle} (hv : s.bundle b.hash = .Verified) :
    exec .deployed (b.calls + 2) (.entry (.executeBundle b false) (List.replicate b.calls .returns))
        s =
      some (beforeCalls .deployed b (s.verifyIfUnreceived b.hash),
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]) := by
  show exec .deployed (b.calls + 1 + 1) _ s = _
  simp only [exec]
  rw [exec_calls_returns .deployed b.hash _ _ _ _ (fun c hc => (List.mem_replicate.1 hc).2)
    (by simp)]
  simp [hv]

lemma txAll_replicate_returns {P : Entry → Prop} {e : Entry} (he : P e) (fuel n : ℕ) :
    TxAll P ⟨fuel, e, List.replicate n .returns⟩ :=
  ⟨he, fun c hc => by rw [(List.mem_replicate.1 hc).2]; exact .returns⟩

theorem ProvableBytesBypassTheFlowGate : Properties.ProvableBytesBypassTheFlowGate := by
  intro s b hu
  refine ⟨fun fuel cs => ?_, txAll_replicate_returns (fun h => h) _ _, ?_⟩
  · cases fuel with
    | zero => rfl
    | succ n => simp [submit, exec, commit]
  · simp only [submit, freshPublicRun]
    rw [exec_public_fresh hu]
    rfl

theorem VerifiedBundleRunsWithoutAnyGate : Properties.VerifiedBundleRunsWithoutAnyGate := by
  intro s b hv
  refine ⟨fun fuel gate cs => ?_,
    txAll_replicate_returns ⟨fun h => Bool.false_ne_true h.2, fun h => h⟩ _ _, ?_⟩
  · cases fuel with
    | zero => rfl
    | succ n => simp [submit, exec, commit, hv]
  · simp only [submit, provelessPublicRun]
    rw [exec_public_verified hv]
    rfl

theorem FlowGateRoutesWitness : Properties.FlowGateRoutesWitness := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;>
      exact ⟨fun h => h, fun c hc => by cases hc⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    exact ⟨fun h => h, fun c hc => by cases hc⟩

end Contracts.InteropHandler.Faithful.History
