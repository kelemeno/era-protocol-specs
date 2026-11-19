import EraSpec.Contracts.PriorityTree.Specs.Library
import EraSpec.Contracts.PriorityTree.Specs.SegmentBinding

/-!
# Properties: the library model's `processBatch` is SegmentBinding's

`../Specs/Library.lean` models the whole `PriorityTree` library with `calculateRootPaths` as a
parameter (`TreeParams.rootPaths`); `../Specs/SegmentBinding.lean` models `processBatch`
(`PT:83-96`) on `unprocessedIndex` and `historicalRoots` with `calculateRootPaths` transcribed
(`MerkleSpec.RootPaths.rootPathsMem`). The statement below ties the two: with the parameter set
to that transcription, the library's `processBatch` reverts exactly when SegmentBinding's does,
and otherwise writes exactly SegmentBinding's new `unprocessedIndex` and nothing else. So the
SegmentBinding results (`ProcessedRunIsQueueSegmentOrBreak` and the others) apply to the
`processBatch` steps of the library model, which `Protocol/PriorityMirror` runs. Proof:
`../Proofs/Library.lean`. No hash premise.
-/

namespace Contracts.PriorityTree.Library

/-- **THE LIBRARY'S `processBatch` IS SEGMENTBINDING'S.** For every node hash `h`, every tree `t`
and every batch, if the library's `calculateRootPaths` parameter is the transcription
`MerkleSpec.RootPaths.rootPaths h`, then the library's `processBatch` returns the tree `t` with
`unprocessedIndex` replaced by the index SegmentBinding's `processBatch` returns (on the same
`historicalRoots`, `unprocessedIndex` and batch), and reverts exactly when that call reverts. The
other fields of the tree (`startIndex`, `historicalRoots`, the Merkle tree) are unchanged. -/
def Properties.LibraryProcessBatchIsSegmentBinding : Prop :=
  ∀ (h : UInt256 → UInt256 → UInt256) (P : TreeParams) (t : PTree) (info : BatchInfo),
    P.rootPaths = MerkleSpec.RootPaths.rootPaths h →
      t.processBatch P info
        = (SegmentBinding.processBatch h t.historicalRoots t.unprocessedIndex
              ⟨info.leftPath, info.rightPath, info.itemHashes⟩).map
            (fun r => { t with unprocessedIndex := r.1 })

end Contracts.PriorityTree.Library
