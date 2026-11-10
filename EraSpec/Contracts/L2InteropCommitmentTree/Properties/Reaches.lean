import EraSpec.Contracts.L2InteropCommitmentTree.Specs.Reaches

/-!
# Properties: batch-sized steps

Statements about `Reaches` (`Specs/Reaches.lean`); proofs in `Proofs/Reaches.lean`.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-- Validity survives any number of guarded inserts — the batch-sized step. -/
def Properties.ReachesValid : Prop :=
  ∀ (T U : Tree), Reaches T U → Valid T → Valid U

/-- **THE KEY SET ONLY GROWS.**  Over any number of guarded inserts, no key is ever
removed: a value committed in one batch is still committed in every later one.  This
is the append-only content of the IMT's *finality signal* — a leg's commitment cannot
be revoked by later batches. -/
def Properties.ReachesKeysMono : Prop :=
  ∀ (T U : Tree), Reaches T U → Valid T → keys (toAbs T) ⊆ keys (toAbs U)

end Contracts.InteropCommitmentTree
