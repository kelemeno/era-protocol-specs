import EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearch

/-!
# Properties: the hint search — what a successful call establishes, and liveness

`Properties/Model.lean` has the safety half of the search (`lowSearch_window`,
`lowSearch_sound`).  This topic adds that the contract's own insert flow yields the
guard the rest of the theory assumes, that `leafCount` hops always suffice, and
that the deployed constant fuel can make an honest insert revert.  Proofs in
`Proofs/HintSearch.lean`.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-- The contract's actual `insert` flow — the three up-front reverts, then the
search from the caller's hint — establishes `InsertGuard` at the index the search
returns.  So the guarded `insert` the rest of the theory is about is exactly what
a successful call performs. -/
def Properties.SearchYieldsGuard : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (fuel i j : ℕ),
    Initialized T → v ≠ 0 → T.valueToIndex v = 0 →
    i < T.leafCount → (T.leaf i).value < v → lowSearch T v fuel i = some j →
    InsertGuard T v j

/-- **THE SEARCH TERMINATES WITH ENOUGH FUEL.**  From any occupied hint, `leafCount`
hops suffice to reach a leaf whose successor is not below `v` — so a correct low
leaf always exists and the walk finds it, for every value and every starting hint.

Values strictly increase along `nextIndex` links (`WindowPos` plus `linkAgree`) and
there are finitely many leaves, so each hop removes one leaf from the interval
between the current value and `v`.  This is the liveness half of the hint
mechanism; `lowSearch_sound` and `lowSearch_window` are the safety half. -/
def Properties.LowSearchTerminates : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (i : ℕ), i < T.leafCount →
    ∃ j, lowSearch T v T.leafCount i = some j

/-- **BUT THE DEPLOYED FUEL IS A CONSTANT, AND THE REVERT IS REACHABLE.**
`MAX_LOW_INDEX_SEARCH_ATTEMPTS` does not scale with `leafCount`, so a hint far
enough from the right place makes `insert` revert with `IMTLowLeafNextTooSmall`
even though a correct low leaf exists.  Minimal witness: a two-leaf tree, where
zero hops revert and one hop succeeds.

This is a liveness caveat, not a safety defect — the caller retries with a fresh
hint — and it is why `Properties.LowSearchTerminates` is stated with `leafCount` fuel rather
than the contract's constant.  The general statement (for every fixed `k`, a tree
needing more than `k` hops) needs an inductively built chain of leaves and is not
constructed here. -/
def Properties.LowSearchCanRevert : Prop :=
  ∀ (a v : UInt256), 0 < a → a < v →
    lowSearch (insert setup a 0) v 0 0 = none
      ∧ lowSearch (insert setup a 0) v 1 0 = some 1

end Contracts.InteropCommitmentTree
