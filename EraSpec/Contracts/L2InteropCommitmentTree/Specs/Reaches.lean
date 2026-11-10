import EraSpec.Contracts.L2InteropCommitmentTree.Specs.Model

/-!
# Contract spec: batch-sized steps of the commitment tree

`Run` (in `Specs/Model.lean`) is one insert or one no-op per step.  A settled batch
is any number of guarded inserts, and the cross-batch results in
`../../../Protocol/InteropAtomicity/` are stated over that.  `Reaches T U` says `U`
is `T` after finitely many guarded inserts.

Ported from the `claude/proof-attempt-4f3778` line (it sat in that line's
`Contracts/InteropCommitmentTree.lean`); the rest of that file is identical to
`Specs/Model.lean`.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-- `U` is reachable from `T` by finitely many guarded inserts — one batch's worth
of `insert` calls. -/
inductive Reaches : Tree → Tree → Prop
  | refl {T} : Reaches T T
  | tail {T U} (h : Reaches T U) {v : UInt256} {low : ℕ} (hg : InsertGuard U v low) :
      Reaches T (insert U v low)

end Contracts.InteropCommitmentTree
