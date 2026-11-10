import EraSpec.Contracts.L2InteropCommitmentTree.Properties.Reaches
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Model

/-! # Proofs: batch-sized steps -/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-- A value is a key exactly when some occupied index carries it. -/
lemma mem_keys_iff_index {T : Tree} {v : UInt256} :
    v ∈ keys (toAbs T) ↔ ∃ i < T.leafCount, (T.leaf i).value = v := by
  constructor
  · intro hmem
    obtain ⟨X, hX, hXv⟩ := Finset.mem_image.mp hmem
    obtain ⟨i, hi, hival, _⟩ := mem_toAbs.mp hX
    exact ⟨i, hi, hival.trans hXv⟩
  · rintro ⟨i, hi, hval⟩
    exact Finset.mem_image.mpr
      ⟨⟨v, (T.leaf i).nextValue⟩, mem_toAbs.mpr ⟨i, hi, hval, rfl⟩, rfl⟩

theorem reaches_valid {T U : Tree} (h : Reaches T U) (h0 : Valid T) : Valid U := by
  induction h with
  | refl => exact h0
  | tail _ hg ih => exact insert_preserves_valid ih hg

theorem reaches_keys_mono {T U : Tree} (h : Reaches T U) (h0 : Valid T) :
    keys (toAbs T) ⊆ keys (toAbs U) := by
  induction h with
  | refl => exact fun _ hx => hx
  | @tail U hr v low hg ih =>
    intro x hx
    rw [(insert_sound_step (reaches_valid hr h0) hg).2]
    exact Finset.mem_insert_of_mem (ih hx)

theorem ReachesValid : Properties.ReachesValid := @reaches_valid
theorem ReachesKeysMono : Properties.ReachesKeysMono := @reaches_keys_mono

end Contracts.InteropCommitmentTree
