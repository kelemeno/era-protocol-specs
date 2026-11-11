import EraSpec.Protocol.MultichainGate.Properties.Model
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Model

/-!
# Multi-chain refund gate: proofs

Certificates for `EraSpec.Protocol.MultichainGate.Properties.Model`.  The
positive direction is `present_not_reclaimable` applied to the source chain
alone; the countermodels are built from genesis by guarded inserts, so their
soundness / validity is inherited rather than asserted.
-/

namespace Contracts.Protocol

open IMTAbstract

/-! ## The bound gate is safe -/

theorem bound_gate_excludes_delivered {P : Protocol} {src : Chain} {v : UInt256}
    (hsound : SoundState (P.trees src)) (hdel : Delivered P src v) :
    Properties.bound_gate_excludes_delivered (P := P) (src := src) (v := v) hsound hdel := by
  unfold Properties.bound_gate_excludes_delivered
  exact present_not_reclaimable hsound.1 hdel

theorem bound_gate_excludes_delivered' {P : Protocol} (hP : AllSound P)
    {src : Chain} {v : UInt256} (hdel : Delivered P src v) :
    Properties.bound_gate_excludes_delivered' (P := P) hP (src := src) (v := v) hdel := by
  unfold Properties.bound_gate_excludes_delivered'
  exact bound_gate_excludes_delivered (hP src) hdel

theorem no_double_spend_multichain {P : Protocol} (hP : AllSound P)
    {src : Chain} {v : UInt256} :
    Properties.no_double_spend_multichain (P := P) hP (src := src) (v := v) := by
  unfold Properties.no_double_spend_multichain
  rintro ⟨hdel, hgate⟩
  exact bound_gate_excludes_delivered' hP hdel hgate

/-! ## The unbound gate is exploitable -/

lemma genesis_mem : (⟨0, 0⟩ : AbsLeaf) ∈ ({⟨0, 0⟩} : Finset AbsLeaf) :=
  Finset.mem_singleton_self _

/-- `v` is fresh at genesis whenever it is nonzero. -/
lemma genesis_fresh {v : UInt256} (hv : 0 < v) : v ∉ keys ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro hmem
  obtain ⟨X, hX, hXv⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hX
  subst hX
  have hz : (0 : UInt256) = v := hXv
  exact absurd hz (ne_of_lt hv)

theorem attackProtocol_allSound {v : UInt256} (hv : 0 < v) :
    Properties.attackProtocol_allSound (v := v) hv := by
  unfold Properties.attackProtocol_allSound
  intro c
  unfold attackProtocol
  by_cases hc : c = 0
  · simp only [hc, if_pos rfl]
    exact (guarded_insert_sound_step genesis_soundState genesis_mem hv
      (Or.inl rfl) (genesis_fresh hv)).1
  · simp only [if_neg hc]
    exact genesis_soundState

theorem attackProtocol_delivered {v : UInt256} :
    Properties.attackProtocol_delivered (v := v) := by
  unfold Properties.attackProtocol_delivered
  unfold Delivered attackProtocol
  simp only [if_pos rfl]
  exact imtInsert_key_mem genesis_mem

theorem attackProtocol_witness_elsewhere {v : UInt256} (hv : 0 < v) :
    Properties.attackProtocol_witness_elsewhere (v := v) hv := by
  unfold Properties.attackProtocol_witness_elsewhere
  refine ⟨⟨0, 0⟩, ?_, hv, Or.inl rfl⟩
  unfold attackProtocol
  simp only [if_neg (by decide : ¬ (1 : Chain) = 0)]
  exact genesis_mem

theorem unbound_gate_refunds_delivered_leg {v : UInt256} (hv : 0 < v) :
    Properties.unbound_gate_refunds_delivered_leg (v := v) hv := by
  unfold Properties.unbound_gate_refunds_delivered_leg
  exact ⟨attackProtocol_allSound hv, attackProtocol_delivered,
    ⟨1, attackProtocol_witness_elsewhere hv⟩⟩

theorem binding_is_exactly_what_separates_them {v : UInt256} (hv : 0 < v) :
    Properties.binding_is_exactly_what_separates_them (v := v) hv := by
  unfold Properties.binding_is_exactly_what_separates_them
  exact ⟨bound_gate_excludes_delivered' (attackProtocol_allSound hv) attackProtocol_delivered,
    ⟨1, attackProtocol_witness_elsewhere hv⟩⟩

theorem bound_gate_not_dead {v : UInt256} (hv : 0 < v) :
    Properties.bound_gate_not_dead (v := v) hv := by
  unfold Properties.bound_gate_not_dead
  exact ⟨attackProtocol_allSound hv, attackProtocol_delivered,
    attackProtocol_witness_elsewhere hv⟩

/-! ## Lifting real contract states -/

open Contracts.InteropCommitmentTree in
theorem chains_no_double_spend {T : Chain → Tree} (hV : ∀ c, Valid (T c))
    {src : Chain} {v : UInt256} :
    Properties.chains_no_double_spend (T := T) hV (src := src) (v := v) := by
  unfold Properties.chains_no_double_spend
  refine no_double_spend_multichain ?_
  intro c
  exact (hV c).absSound

open Contracts.InteropCommitmentTree in
/-- A valid tree's key set contains the sentinel value `0`. -/
lemma zero_mem_keys_toAbs {T : Tree} (hV : Valid T) : (0 : UInt256) ∈ keys (toAbs T) := by
  unfold keys
  refine Finset.mem_image.mpr ⟨⟨(T.leaf 0).value, (T.leaf 0).nextValue⟩, ?_, hV.sentinel⟩
  exact mem_toAbs.mpr ⟨0, hV.occupied, rfl, rfl⟩

open Contracts.InteropCommitmentTree in
theorem chains_bound_gate_iff_undelivered {T : Chain → Tree} {src : Chain}
    (hV : Valid (T src)) {v : UInt256} (hv : v ≠ 0) :
    Properties.chains_bound_gate_iff_undelivered (T := T) (src := src) hV (v := v) hv := by
  unfold Properties.chains_bound_gate_iff_undelivered
  -- The constant history at this one state is an `Evolution`; apply
  -- `reclaimable_iff_absent` at snapshot 0.
  exact reclaimable_iff_absent (S := fun _ => toAbs (T src)) (fun _ => Or.inl rfl)
    hV.absSound (zero_mem_keys_toAbs hV) (j := 0) hv

open Contracts.InteropCommitmentTree in
/-- `insert(v, 0)` on a fresh `setup` passes the contract's guard. -/
lemma setup_insert_guard {v : UInt256} (hv : 0 < v) : InsertGuard setup v 0 where
  initialized := one_ne_zero
  nonzero := ne_of_gt hv
  fresh := rfl
  inBounds := Nat.zero_lt_one
  lowBelow := hv
  window := Or.inl rfl

open Contracts.InteropCommitmentTree in
theorem attackChains_valid {v : UInt256} (hv : 0 < v) :
    Properties.attackChains_valid (v := v) hv := by
  unfold Properties.attackChains_valid
  intro c
  unfold attackChains
  by_cases hc : c = 0
  · simp only [hc, if_pos rfl]
    exact insert_preserves_valid setup_valid (setup_insert_guard hv)
  · simp only [if_neg hc]
    exact setup_valid

open Contracts.InteropCommitmentTree in
theorem chains_unbound_gate_refunds_delivered_leg {v : UInt256} (hv : 0 < v) :
    Properties.chains_unbound_gate_refunds_delivered_leg (v := v) hv := by
  unfold Properties.chains_unbound_gate_refunds_delivered_leg
  have hval : ∀ c, Valid (attackChains v c) := attackChains_valid hv
  have hdel : Delivered (ofChains (attackChains v)) 0 v := by
    show v ∈ keys (toAbs (attackChains v 0))
    have h0 : attackChains v 0 = Contracts.InteropCommitmentTree.insert setup v 0 := by
      unfold attackChains; exact if_pos rfl
    rw [h0, (insert_sound_step setup_valid (setup_insert_guard hv)).2]
    exact Finset.mem_insert_self _ _
  have hw1 : BoundGate (ofChains (attackChains v)) 1 v := by
    have h1 : attackChains v 1 = setup := by
      unfold attackChains; simp only [if_neg (by decide : ¬ (1 : Chain) = 0)]
    show ∃ W ∈ toAbs (attackChains v 1), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)
    rw [h1, toAbs_setup]
    exact ⟨⟨0, 0⟩, genesis_mem, hv, Or.inl rfl⟩
  have hsep : ¬ BoundGate (ofChains (attackChains v)) 0 v := fun hg =>
    chains_no_double_spend hval ⟨hdel, hg⟩
  exact ⟨hval, hdel, ⟨1, hw1⟩, hsep, hw1⟩

end Contracts.Protocol
