import EraSpec.Properties.Protocol
import EraSpec.Proofs.InteropCommitmentTree

/-!
# Proofs: the multi-chain protocol

Proofs of `EraSpec.Properties.Protocol`.  The positive direction is one chain's
exclusivity (`IMTAbstract.present_not_reclaimable`); the countermodel is an
explicit two-chain configuration built by a genuine guarded insert.
-/

namespace Contracts.Protocol

open IMTAbstract

/-! ## The bound gate is safe -/

theorem bound_gate_excludes_delivered {P : Protocol} {src : Chain} {v : UInt256}
    (hsound : SoundState (P.trees src)) (hdel : Delivered P src v) :
    ¬ BoundGate P src v :=
  present_not_reclaimable hsound.1 hdel

theorem bound_gate_excludes_delivered' {P : Protocol} (hP : AllSound P)
    {src : Chain} {v : UInt256} (hdel : Delivered P src v) :
    ¬ BoundGate P src v :=
  bound_gate_excludes_delivered (hP src) hdel

theorem no_double_spend_multichain {P : Protocol} (hP : AllSound P)
    {src : Chain} {v : UInt256} :
    ¬ (Delivered P src v ∧ BoundGate P src v) := by
  rintro ⟨hdel, hgate⟩
  exact bound_gate_excludes_delivered' hP hdel hgate

/-! ## The unbound gate is exploitable -/

lemma genesis_mem : (⟨0, 0⟩ : AbsLeaf) ∈ ({⟨0, 0⟩} : Finset AbsLeaf) :=
  Finset.mem_singleton_self _

lemma genesis_fresh {v : UInt256} (hv : 0 < v) : v ∉ keys ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro hmem
  obtain ⟨X, hX, hXv⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hX
  subst hX
  have hz : (0 : UInt256) = v := hXv
  exact absurd hz (ne_of_lt hv)

theorem attackProtocol_allSound {v : UInt256} (hv : 0 < v) :
    AllSound (attackProtocol v) := by
  intro c
  unfold attackProtocol
  by_cases hc : c = 0
  · simp only [hc, if_pos rfl]
    exact (guarded_insert_sound_step genesis_soundState genesis_mem hv
      (Or.inl rfl) (genesis_fresh hv)).1
  · simp only [if_neg hc]
    exact genesis_soundState

theorem attackProtocol_delivered {v : UInt256} :
    Delivered (attackProtocol v) 0 v := by
  unfold Delivered attackProtocol
  simp only [if_pos rfl]
  exact imtInsert_key_mem genesis_mem

theorem attackProtocol_witness_elsewhere {v : UInt256} (hv : 0 < v) :
    AbsenceWitnessAt (attackProtocol v) 1 v := by
  refine ⟨⟨0, 0⟩, ?_, hv, Or.inl rfl⟩
  unfold attackProtocol
  simp only [if_neg (by decide : ¬ (1 : Chain) = 0)]
  exact genesis_mem

theorem unbound_gate_refunds_delivered_leg {v : UInt256} (hv : 0 < v) :
    AllSound (attackProtocol v)
      ∧ Delivered (attackProtocol v) 0 v
      ∧ UnboundGate (attackProtocol v) v :=
  ⟨attackProtocol_allSound hv, attackProtocol_delivered,
   ⟨1, attackProtocol_witness_elsewhere hv⟩⟩

theorem binding_is_exactly_what_separates_them {v : UInt256} (hv : 0 < v) :
    ¬ BoundGate (attackProtocol v) 0 v
      ∧ UnboundGate (attackProtocol v) v :=
  ⟨bound_gate_excludes_delivered' (attackProtocol_allSound hv) attackProtocol_delivered,
   ⟨1, attackProtocol_witness_elsewhere hv⟩⟩

/-! ## Lifting real contract states -/

open Contracts.InteropCommitmentTree in
theorem chains_no_double_spend {T : Chain → Tree} (hV : ∀ c, Valid (T c))
    {src : Chain} {v : UInt256} :
    ¬ (Delivered (ofChains T) src v ∧ BoundGate (ofChains T) src v) := by
  refine no_double_spend_multichain ?_
  intro c
  exact (hV c).absSound

end Contracts.Protocol

/-! ## Certificates -/

namespace Proofs.Protocol

open Contracts.Protocol

theorem BoundGateExcludesDelivered : Properties.Protocol.BoundGateExcludesDelivered :=
  @bound_gate_excludes_delivered
theorem BoundGateExcludesDelivered' : Properties.Protocol.BoundGateExcludesDelivered' :=
  @bound_gate_excludes_delivered'
theorem NoDoubleSpendMultichain : Properties.Protocol.NoDoubleSpendMultichain :=
  @no_double_spend_multichain
theorem ChainsNoDoubleSpend : Properties.Protocol.ChainsNoDoubleSpend := @chains_no_double_spend
theorem AttackProtocolAllSound : Properties.Protocol.AttackProtocolAllSound :=
  @attackProtocol_allSound
theorem AttackProtocolDelivered : Properties.Protocol.AttackProtocolDelivered :=
  @attackProtocol_delivered
theorem AttackProtocolWitnessElsewhere : Properties.Protocol.AttackProtocolWitnessElsewhere :=
  @attackProtocol_witness_elsewhere
theorem UnboundGateRefundsDeliveredLeg : Properties.Protocol.UnboundGateRefundsDeliveredLeg :=
  @unbound_gate_refunds_delivered_leg
theorem BindingIsExactlyWhatSeparatesThem :
    Properties.Protocol.BindingIsExactlyWhatSeparatesThem :=
  @binding_is_exactly_what_separates_them

end Proofs.Protocol
