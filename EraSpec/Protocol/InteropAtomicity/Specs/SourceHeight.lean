import EraSpec.Protocol.InteropAtomicity.Specs.Atomicity
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight

/-!
# Model: systems whose heights are the trees' own `FullMerkle._height`

`System.height` (in `Specs/Atomicity.lean`) is a free field, and `Wf.capacity`
assumes it fits the tree.  In the deployed contract each chain's commitment tree
carries its own `FullMerkle._height`, grown by `pushNewLeaf`
(`Contracts/L2InteropCommitmentTree/Specs/RunHeight.lean`).  This file builds systems
from per-chain, per-batch contract states that carry their dimensions, so the height
is read off the state rather than supplied.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.SourceHeight`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.SourceHeight`.

## Model boundary

The height is the modelled `_height` of the IMT's `FullMerkle` tree at each batch end.
That `IMT_END_ROOT_LEAF_INDEX` / `IMT_BEGIN_ROOT_LEAF_INDEX` record the root at that
height is the same O7 obligation as for `TreeRoot`; it is not proved here.  The batch
root tree that `Specs/Timeout.lean` carries (with its own `capacity` field) is a
different tree and is not covered.
-/

namespace Contracts.Atomicity

open Contracts.InteropCommitmentTree

/-- The system whose chain `c`, batch `n` tree and height are those of the contract
state `St c n` (list state plus `FullMerkle` dimensions). -/
def systemOfRuns (St : Chain → ℕ → HState) (time : Chain → ℕ → ℕ) : System where
  tree := fun c n => (St c n).tree
  time := time
  height := fun c n => (St c n).height

/-- The run-level counterpart of `Wf`'s first three fields, on states that carry their
dimensions: every chain starts at `hSetup` and may insert during batch 0, each batch
applies any number of guarded inserts, and batch timestamps are monotone.  There is no
capacity field. -/
structure RunsWf (St : Chain → ℕ → HState) (time : Chain → ℕ → ℕ) : Prop where
  start : ∀ c, HReaches hSetup (St c 0)
  batch : ∀ c n, HReaches (St c n) (St c (n + 1))
  timeOrdered : ∀ c, Monotone (time c)

/-- Every batch's height is the `FullMerkle._height` the source reaches for that
batch's leaf count. -/
def HeightsFromSource (S : System) : Prop :=
  ∀ c n, S.height c n = fmHeight (S.tree c n).leafCount

end Contracts.Atomicity
