import EraSpec.Contracts.L2InteropCommitmentTree.Specs.Reaches

/-!
# Contract spec: the hint search

`lowSearch` and `InsertGuard` are defined in `Specs/Model.lean`; this topic needs
no further definitions.  `MAX_LOW_INDEX_SEARCH_ATTEMPTS` is the deployed fuel.
-/

namespace Contracts.InteropCommitmentTree

/-- `MAX_LOW_INDEX_SEARCH_ATTEMPTS` in `contracts/common/Config.sol` at the pin.  The
contract's loop allows this many hops and reverts with `IMTLowLeafNextTooSmall` when
one more is needed, which is `lowSearch` with this fuel. -/
def maxLowIndexSearchAttempts : ℕ := 5

/-- The honest run `setup; insert 1; insert 2; …; insert n`, each insert given the
correct low leaf (the previous index).  Leaf `k` carries value `k`. -/
def chainTree : ℕ → Tree
  | 0 => setup
  | n + 1 => insert (chainTree n) ((n + 1 : ℕ) : UInt256) n

end Contracts.InteropCommitmentTree
