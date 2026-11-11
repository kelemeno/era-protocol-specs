import EraSpec.Contracts.FullMerkle.Properties.TreeShapeStrong
import EraSpec.Contracts.Merkle.Proofs.RootForgeryPinnedStrong

/-!
# Proofs: the padding ambiguity, within capacity and located

Proofs of `EraSpec.Contracts.FullMerkle.Properties.TreeShapeStrong`.  The engine is
`MerkleSpec.Pinned.same_tree_of_getD_eq` (lists that agree at every entry read with the padding
default are the same tree at every height, with no collision on any path) applied to `L` and
`L ++ replicate k z0`, which agree there by `MerkleSpec.PinnedStrong.getD_append_replicate_pad`.
-/

namespace AttackVectors.TreeShapeStrong

open Clear MerkleSpec MerkleSpec.Verifier MerkleSpec.Pinned MerkleSpec.PinnedStrong

theorem rootOf_append_padding (h : Hash) (z0 : UInt256) (L : List UInt256) (k height : ℕ) :
    Properties.rootOf_append_padding h z0 L k height :=
  (same_tree_of_getD_eq h z0 _ _ (getD_append_replicate_pad z0 L k) height).1

theorem padding_ambiguity_within_capacity (h : Hash) (z0 : UInt256) (L : List UInt256)
    (k height : ℕ) (hk : 0 < k) (hcap : (L ++ List.replicate k z0).length ≤ 2 ^ height) :
    Properties.padding_ambiguity_within_capacity h z0 L k height hk hcap := by
  have hlen : (L ++ List.replicate k z0).length = L.length + k := by
    simp only [List.length_append, List.length_replicate]
  have hsame := same_tree_of_getD_eq h z0 L (L ++ List.replicate k z0)
    (fun j => (getD_append_replicate_pad z0 L k j).symm) height
  refine ⟨by omega, by omega, fun he => ?_, hsame.1, Or.inl ⟨by omega, ?_⟩, hsame.2⟩
  · have hl := congrArg List.length he
    omega
  · rw [getD_append_replicate_pad]
    exact getD_default L L.length z0 le_rfl

theorem padding_twin_exists_iff_not_full (z0 : UInt256) (L : List UInt256) (height : ℕ) :
    Properties.padding_twin_exists_iff_not_full z0 L height := by
  constructor
  · rintro ⟨k, hk, hcap⟩
    simp only [List.length_append, List.length_replicate] at hcap
    omega
  · intro hlt
    refine ⟨2 ^ height - L.length, by omega, ?_⟩
    simp only [List.length_append, List.length_replicate]
    omega

theorem padding_ambiguity_forges_root_pinned (h : Hash) (z0 a : UInt256) :
    Properties.padding_ambiguity_forges_root_pinned h z0 a := by
  obtain ⟨hcap₁, hlen, hne, hroot, _, hnc⟩ :=
    padding_ambiguity_within_capacity h z0 [a] 1 1 (by decide) (by simp)
  exact ⟨hcap₁, by simp, hlen, hne, hroot, hnc⟩

theorem padding_ambiguity_within_capacity_satisfiable (z0 a : UInt256) :
    Properties.padding_ambiguity_within_capacity_satisfiable z0 a :=
  ⟨by simp, by decide, by simp⟩

end AttackVectors.TreeShapeStrong
