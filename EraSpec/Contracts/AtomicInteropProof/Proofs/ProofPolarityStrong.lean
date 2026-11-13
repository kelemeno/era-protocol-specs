import EraSpec.Contracts.AtomicInteropProof.Properties.ProofPolarityStrong
import EraSpec.Contracts.AtomicInteropProof.Proofs.ProofPolarity
import EraSpec.Protocol.MultichainGate.Proofs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Model
import Mathlib.Tactic

/-!
# Proofs: proof polarity, stated against the gates

Certificates for `EraSpec.Contracts.AtomicInteropProof.Properties.ProofPolarityStrong`.  The
abstract statements are proved from `HonestInsertion` directly.  The contract-level ones reduce
to `Contracts.Protocol.chains_bound_gate_iff_undelivered`.  That result says that on a valid
commitment tree, a nonzero value has an IMT non-inclusion witness iff it is not a key.  The
witness state is `Contracts.Protocol.attackChains`.
-/

namespace AttackVectors.ProofPolarity


section Abstract

variable {Chain Value : Type*}

variable (srcOf : Value → Chain)

variable (tree : Chain → Set Value)


/-! ## The refund gate with the comparison -/

theorem checked_absence_gate_rejects_live_leg {v : Value} (hlive : v ∈ tree (srcOf v)) :
    Properties.checked_absence_gate_rejects_live_leg srcOf tree hlive := by
  unfold Properties.checked_absence_gate_rejects_live_leg
  rintro c ⟨rfl, habs⟩
  exact habs hlive


theorem checked_absence_gate_iff_absent (declared : Chain) (v : Value) :
    Properties.checked_absence_gate_iff_absent tree declared v := by
  unfold Properties.checked_absence_gate_iff_absent
  constructor
  · rintro ⟨c, rfl, habs⟩
    exact habs
  · intro habs
    exact ⟨declared, rfl, habs⟩


/-! ## The inclusion path -/

theorem unchecked_inclusion_gate_iff_checked (h : HonestInsertion srcOf tree) (v : Value) :
    Properties.unchecked_inclusion_gate_iff_checked srcOf tree h v := by
  unfold Properties.unchecked_inclusion_gate_iff_checked
  constructor
  · -- a membership proof against `c` pins `c` to the leg's chain
    rintro ⟨c, hmem⟩
    exact ⟨c, (h c v hmem).symm, hmem⟩
  · rintro ⟨c, -, hmem⟩
    exact ⟨c, hmem⟩


/-! ## The refund path without the comparison -/

theorem unchecked_absence_gate_iff (h : HonestInsertion srcOf tree) (v : Value) :
    Properties.unchecked_absence_gate_iff srcOf tree h v := by
  unfold Properties.unchecked_absence_gate_iff
  constructor
  · rintro ⟨c, habs⟩
    by_cases hc : c = srcOf v
    · subst hc
      exact Or.inr habs
    · exact Or.inl ⟨c, hc⟩
  · rintro (⟨c, hc⟩ | habs)
    · -- a foreign chain never holds the value, so its tree supplies the absence
      exact ⟨c, fun hmem => hc (h c v hmem).symm⟩
    · exact ⟨srcOf v, habs⟩


theorem unchecked_absence_gate_accepts_every_leg (h : HonestInsertion srcOf tree)
    {c₀ c₁ : Chain} (hne : c₀ ≠ c₁) :
    Properties.unchecked_absence_gate_accepts_every_leg srcOf tree h hne := by
  unfold Properties.unchecked_absence_gate_accepts_every_leg
  intro v
  -- one of the two chains is not `v`'s own
  have hforeign : ∃ c, c ≠ srcOf v := by
    by_cases h₀ : c₀ = srcOf v
    · exact ⟨c₁, fun h₁ => hne (h₀.trans h₁.symm)⟩
    · exact ⟨c₀, h₀⟩
  obtain ⟨c, hc⟩ := hforeign
  exact ⟨c, hc, fun hmem => hc (h c v hmem).symm⟩


theorem polarity_asymmetry (h : HonestInsertion srcOf tree)
    {c₀ c₁ : Chain} (hne : c₀ ≠ c₁) :
    Properties.polarity_asymmetry srcOf tree h hne := by
  unfold Properties.polarity_asymmetry
  refine ⟨fun v => unchecked_inclusion_gate_iff_checked srcOf tree h v, fun v hlive => ⟨?_, ?_⟩⟩
  · obtain ⟨c, -, habs⟩ := unchecked_absence_gate_accepts_every_leg srcOf tree h hne v
    exact ⟨c, habs⟩
  · rintro ⟨c, hc⟩
    exact checked_absence_gate_rejects_live_leg srcOf tree hlive c hc

end Abstract


/-! ## Non-vacuity, and the role of honesty -/

theorem finalized_leg_passes_unchecked_absence_gate :
    Properties.finalized_leg_passes_unchecked_absence_gate := by
  unfold Properties.finalized_leg_passes_unchecked_absence_gate
  -- two chains; every value originates on `true`, and only `true`'s tree holds it
  refine ⟨Bool, Unit, fun _ => true, fun c => {_x | c = true}, (), false, ?_, ?_, ?_, ?_⟩
  · intro c v hmem
    exact (show c = true from hmem).symm
  · exact ⟨rfl, rfl⟩
  · intro hmem
    exact Bool.false_ne_true hmem
  · rintro ⟨c', rfl, habs⟩
    exact habs rfl


theorem honest_polarity_model_exists :
    Properties.honest_polarity_model_exists := by
  unfold Properties.honest_polarity_model_exists
  -- values are `Bool`s originating on chain `true`; chain `true` holds only the value `true`
  refine ⟨Bool, Bool, fun _ => true, fun c => {x | c = true ∧ x = true}, true, false, true, false,
    ?_, ?_, ?_, ?_⟩
  · intro c v hmem
    exact (show c = true ∧ v = true from hmem).1.symm
  · decide
  · exact ⟨rfl, rfl⟩
  · intro hmem
    exact Bool.false_ne_true (show true = true ∧ false = true from hmem).2


theorem unchecked_inclusion_gate_differs_without_honesty :
    Properties.unchecked_inclusion_gate_differs_without_honesty := by
  unfold Properties.unchecked_inclusion_gate_differs_without_honesty
  -- the value originates on `true`, but only the misbehaving chain `false` holds it
  refine ⟨Bool, Unit, fun _ => true, fun c => {_x | c = false}, (), ⟨false, rfl⟩, ?_⟩
  rintro ⟨c, rfl, hmem⟩
  exact Bool.true_eq_false.mp hmem


/-! ## On commitment-tree states -/

/-- A nonzero value is outside `liveKeys T c` iff it is not delivered on `c`. -/
private lemma not_mem_liveKeys_iff
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    {c : Contracts.Protocol.Chain} {v : UInt256} (hv : v ≠ 0) :
    v ∉ liveKeys T c ↔ ¬ Contracts.Protocol.Delivered (Contracts.Protocol.ofChains T) c v := by
  constructor
  · intro hnl hdel
    exact hnl ⟨hv, hdel⟩
  · intro hnd hlive
    exact hnd hlive.2

/-- The bound gate at `c` is the absence of `v` from `liveKeys T c`, on a valid tree. -/
private lemma boundGate_iff_not_mem_liveKeys
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    {c : Contracts.Protocol.Chain} (hV : Contracts.InteropCommitmentTree.Valid (T c))
    {v : UInt256} (hv : v ≠ 0) :
    Contracts.Protocol.BoundGate (Contracts.Protocol.ofChains T) c v ↔ v ∉ liveKeys T c :=
  (Contracts.Protocol.chains_bound_gate_iff_undelivered hV hv).trans
    (not_mem_liveKeys_iff hv).symm


theorem chains_delivered_pins_source
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    {srcOf : UInt256 → Contracts.Protocol.Chain} (h : HonestInsertion srcOf (liveKeys T))
    {c : Contracts.Protocol.Chain} {v : UInt256} (hv : v ≠ 0)
    (hdel : Contracts.Protocol.Delivered (Contracts.Protocol.ofChains T) c v) :
    Properties.chains_delivered_pins_source h hv hdel := by
  unfold Properties.chains_delivered_pins_source
  exact h c v ⟨hv, hdel⟩


theorem chains_bound_gate_iff_checked_absence_gate
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    {src : Contracts.Protocol.Chain} (hV : Contracts.InteropCommitmentTree.Valid (T src))
    {v : UInt256} (hv : v ≠ 0) :
    Properties.chains_bound_gate_iff_checked_absence_gate hV hv := by
  unfold Properties.chains_bound_gate_iff_checked_absence_gate
  exact (boundGate_iff_not_mem_liveKeys hV hv).trans
    (checked_absence_gate_iff_absent (liveKeys T) src v).symm


theorem chains_unbound_gate_iff_unchecked_absence_gate
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    (hV : ∀ c, Contracts.InteropCommitmentTree.Valid (T c)) {v : UInt256} (hv : v ≠ 0) :
    Properties.chains_unbound_gate_iff_unchecked_absence_gate hV hv := by
  unfold Properties.chains_unbound_gate_iff_unchecked_absence_gate
  -- `UnboundGate` is `∃ c, BoundGate _ c v`; rewrite each disjunct on its own valid tree
  exact exists_congr fun c => boundGate_iff_not_mem_liveKeys (hV c) hv


theorem chains_unbound_gate_accepts_every_leg
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    (hV : ∀ c, Contracts.InteropCommitmentTree.Valid (T c))
    {srcOf : UInt256 → Contracts.Protocol.Chain} (h : HonestInsertion srcOf (liveKeys T))
    {v : UInt256} (hv : v ≠ 0) :
    Properties.chains_unbound_gate_accepts_every_leg hV h hv := by
  unfold Properties.chains_unbound_gate_accepts_every_leg
  -- the abstract chain-blindness, at the two chains `0 ≠ 1`, then lifted to the IMT witness
  obtain ⟨c, hc, habs⟩ := unchecked_absence_gate_accepts_every_leg srcOf (liveKeys T) h
    (c₀ := 0) (c₁ := 1) (by decide) v
  exact ⟨c, hc, (boundGate_iff_not_mem_liveKeys (hV c) hv).mpr habs⟩


/-- `setup`'s tree has no nonzero key. -/
private lemma liveKeys_setup_empty
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    {c : Contracts.Protocol.Chain} (hT : T c = Contracts.InteropCommitmentTree.setup)
    {w : UInt256} : w ∉ liveKeys T c := by
  rintro ⟨hw, hkey⟩
  rw [hT, Contracts.InteropCommitmentTree.toAbs_setup] at hkey
  simp [IMTAbstract.keys] at hkey
  exact hw hkey


theorem chains_honest_double_mint_witness :
    Properties.chains_honest_double_mint_witness := by
  unfold Properties.chains_honest_double_mint_witness
  have h01 : (0 : UInt256) < 1 := by decide
  obtain ⟨hval, hdel, hub, hnb, -⟩ :=
    Contracts.Protocol.chains_unbound_gate_refunds_delivered_leg (v := 1) h01
  refine ⟨Contracts.Protocol.attackChains 1, fun _ => 0, 1, hval, ?_, by decide, hdel, hub, hnb⟩
  -- honest insertion: only chain `0` holds a nonzero key, and every value originates there
  intro c w hlive
  by_contra hc
  have hT : Contracts.Protocol.attackChains 1 c = Contracts.InteropCommitmentTree.setup := by
    unfold Contracts.Protocol.attackChains
    exact ite_eq_right (Ne.symm hc)
  exact liveKeys_setup_empty hT hlive


end AttackVectors.ProofPolarity
