import EraSpec.Contracts.L2InteropCommitmentTree.History.Properties.PaddingForgeryPinned
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CachedRoot

/-!
# History proofs: the padding forgery at the interop pin `c67894b9`

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.History.Properties.PaddingForgeryPinned`.
The lemmas are the canonical layers' (`Proofs/TreeRoot.lean`, `Proofs/RunHeight.lean`,
`Proofs/CachedRoot.lean`), which hold for every padding constant.
-/

namespace Contracts.InteropCommitmentTree.History

open IMTAbstract MerkleSpec MerkleSpec.Verifier

theorem PaddingCollisionForgesAbsence : Properties.PaddingCollisionForgesAbsence :=
  @padding_collision_forges_absence

theorem PaddingCollisionRefundsDeliveredLeg :
    Properties.PaddingCollisionRefundsDeliveredLeg :=
  @padding_collision_refunds_delivered_leg

theorem PaddingCountermodelLocatesPaddingHit : Properties.PaddingCountermodelLocatesPaddingHit :=
  padding_countermodel_locates_padding_hit

theorem PaddingCountermodelExactlyPaddingHit : Properties.PaddingCountermodelExactlyPaddingHit :=
  padding_countermodel_exactly_padding_hit

theorem PaddingForgeryAtOwnHeight : Properties.PaddingForgeryAtOwnHeight :=
  padding_forgery_at_own_height

theorem CThreeLeafWitness : Properties.CThreeLeafWitness := cThreeLeaf_witness

end Contracts.InteropCommitmentTree.History
