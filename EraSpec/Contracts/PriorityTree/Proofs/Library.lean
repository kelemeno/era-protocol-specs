import EraSpec.Contracts.PriorityTree.Properties.Library
import EraSpec.Contracts.PriorityTree.Proofs.SegmentBinding

/-!
# Proofs: the library model's `processBatch` is SegmentBinding's

Proof of `../Properties/Library.lean`. Both functions do nothing on an empty batch; otherwise
both run `calculateRootPaths`, check the root is historical and add a length with a checked
`+=`. The library adds the number of items, SegmentBinding the length of the array
`calculateRootPaths` leaves; `MerkleSpec.RootPaths.rootPaths_frame` says the two are equal.
-/

namespace Contracts.PriorityTree.Library

open MerkleSpec.RootPaths

theorem LibraryProcessBatchIsSegmentBinding : Properties.LibraryProcessBatchIsSegmentBinding := by
  intro h P t info hP
  unfold PTree.processBatch SegmentBinding.processBatch
  simp only [hP]
  by_cases hn : info.itemHashes.length = 0
  · simp [hn]
  · have hpos : 0 < info.itemHashes.length := by omega
    simp only [hn, ite_false, hpos, ite_true]
    unfold rootPaths
    cases hm : rootPathsMem h info.leftPath info.rightPath t.unprocessedIndex info.itemHashes with
    | none => simp
    | some p =>
      obtain ⟨r, mem⟩ := p
      have hlen := (rootPaths_frame hm).1
      cases hr : t.historicalRoots r
      · simp [hr]
      · have hw : Contracts.PriorityTree.Library.wordLimit = MerkleSpec.RootPaths.wordLimit := rfl
        simp only [hr, checked, hw, hlen, Bool.true_eq_false, ite_false, ite_true, Option.map_some]
        split_ifs <;> rfl

end Contracts.PriorityTree.Library
