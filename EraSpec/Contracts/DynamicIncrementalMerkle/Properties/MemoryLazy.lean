import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.MemoryLazy

/-!
# Properties: the memory tree, its lazy push, and the stale root after `extendUntilEnd`

Statements about `EraSpec.Contracts.DynamicIncrementalMerkle.Specs.MemoryLazy`.  Proofs are in
`EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.MemoryLazy`.

* **(i) The latent defect.**  `createTree(3); setup(z); pushLazy(a); pushLazy(b); pushLazy(c);
  extendUntilEnd();` leaves `root()` reporting `bytes32(0)`, and the flag that would have made
  `root()` recompute it cleared.  With eager pushes, or with `root()` called before
  `extendUntilEnd`, the same leaves give `h (h a b) (h c z)`.  The third lazy push takes the early
  return (index 2 turns left at level 0) after the growth branch has written `bytes32(0)` into the
  new root slot; `extendUntilEnd` reads that slot as `currentSide` (:174) and clears the flag
  (:184).  No caller at the pin pushes into a memory tree before `extendUntilEnd`, and no caller
  uses `pushLazy` at all: the only use is `L2MessageRoot.getEmptyMultichainBatchRoot`, which
  only runs `createTree(1)` and `setup`.  So this is a latent library defect, not a reachable
  protocol bug.
* **(j) Without `extendUntilEnd` the lazy push is sound.**  Along every run of eager and lazy
  pushes, `root()` returns the fold at the minimal height (`0` while empty), recalculating when
  the flag is set; the flag is set only on a nonempty tree that is not full, which is why the
  growth branch never promotes a stale root slot into a side.  The memory tree reports the same
  root as the storage tree over the same leaves, and an eager memory push returns what the
  storage push returns.

No hash premise is used: every statement holds for every node hash `h` and zero `z`.
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec

/-! ## (i) `extendUntilEnd` after a lazy push -/

/-- **COUNTERMODEL: `pushLazy` THEN `extendUntilEnd` RETURNS A STALE ROOT.**  For every hash and
zero value: after three lazy pushes into a depth-3 tree, `extendUntilEnd` clears the
recalculation flag and `root()` returns `0`; three eager pushes give `h (h a b) (h c z)`; and the
lazy tree's own `root()`, called before `extendUntilEnd`, recalculates the same
`h (h a b) (h c z)`. -/
def Properties.LazyExtendStaleRoot : Prop :=
  ∀ (h : Hash) (z a b c : UInt256),
    ((lazyRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).map MemPushTree.needsRecalc = some false
      ∧ (((lazyRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).bind (mRoot h)).map (·.2) = some 0
      ∧ (((eagerRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).bind (mRoot h)).map (·.2)
          = some (h (h a b) (h c z))
      ∧ ((lazyRun h z 3 [a, b, c]).bind (mRoot h)).map (·.2) = some (h (h a b) (h c z))

/-- **THE STALE ROOT IS WRONG.**  For some hash, the root `extendUntilEnd` leaves after the lazy
pushes differs from the fold over the same leaves at the same height, which is what the eager
run reports. -/
def Properties.LazyExtendStaleRootIsWrong : Prop :=
  ∃ (h : Hash) (z a b c : UInt256),
    (((lazyRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).bind (mRoot h)).map (·.2)
      ≠ some (rootOf h z [a, b, c] 2)
    ∧ (((eagerRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).bind (mRoot h)).map (·.2)
      = some (rootOf h z [a, b, c] 2)

/-! ## (j) Lazy pushes without `extendUntilEnd` -/

/-- **`setup` ESTABLISHES THE MEMORY INVARIANT.**  On a tree allocated with depth `≥ 1`, `setup`
succeeds and represents the empty tree at height 0; with depth `0` it reverts. -/
def Properties.MemSetupRepresentsEmpty : Prop :=
  ∀ (h : Hash) (z : UInt256) (depth : ℕ),
    (depth = 0 → msetup (createTree MemPushTree.fresh depth) z = none)
      ∧ (0 < depth → ∃ T, msetup (createTree MemPushTree.fresh depth) z = some (T, 0)
          ∧ MemRepresents h z [] 0 T)

/-- **AN EAGER OR LAZY PUSH KEEPS THE INVARIANT, AND REVERTS ONLY WHEN OUT OF ROOM.**  From a
memory tree representing `L` at `H`, `_pushInner(x, lazy)` reverts exactly when the tree is full
and the allocation has no slot for the new level; otherwise it returns index `|L|`, represents
`L ++ [x]` at the new height, and, unless it left the flag set (which an eager push never does),
returns the new fold. -/
def Properties.MemPushComputesRoot : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (T : MemPushTree) (x : UInt256)
    (lazy : Bool), MemRepresents h z L H T →
    (L.length = 2 ^ H ∧ T.sides.length ≤ H + 1 → mPushInner h T x lazy = none)
      ∧ (¬ (L.length = 2 ^ H ∧ T.sides.length ≤ H + 1) →
          ∃ (T' : MemPushTree) (r : UInt256), mPushInner h T x lazy = some (T', L.length, r)
            ∧ MemRepresents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) T'
            ∧ (lazy = false → T'.needsRecalc = false)
            ∧ (T'.needsRecalc = false →
                r = rootOf h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H)))

/-- **`root()` RECALCULATES CORRECTLY.**  On a memory tree representing `L` at `H`, `root()`
returns `dimRoot h z L H` (recomputing it from the sides and `_lastLeafValue` when the flag is
set), and leaves the tree representing `L` at `H` with the flag clear. -/
def Properties.MemRootIsFold : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (T : MemPushTree),
    MemRepresents h z L H T →
    ∃ T', mRoot h T = some (T', dimRoot h z L H) ∧ MemRepresents h z L H T'
      ∧ T'.needsRecalc = false

/-- **ALONG RUNS OF EAGER AND LAZY PUSHES, `root()` IS THE FOLD AT THE MINIMAL HEIGHT.**  Every
memory tree reached by `createTree(depth)`, `setup(z)` and successful pushes of `L` (eager or lazy,
in any order) represents `L` at `dimHeight |L|`, and its `root()` returns
`dimRoot h z L (dimHeight |L|)`. -/
def Properties.LazyRootRecalculated : Prop :=
  ∀ (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256) (T : MemPushTree),
    MemRun h z depth L T →
    MemRepresents h z L (dimHeight L.length) T
      ∧ ∃ T', mRoot h T = some (T', dimRoot h z L (dimHeight L.length))
          ∧ T'.needsRecalc = false

/-- **THE FLAG IS SET ONLY ON A NONEMPTY TREE THAT IS NOT FULL.**  So the push that would grow
the tree always finds a correct root slot to turn into a side. -/
def Properties.LazyFlagMeansNotFull : Prop :=
  ∀ (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256) (T : MemPushTree),
    MemRun h z depth L T → T.needsRecalc = true →
      L ≠ [] ∧ L.length < 2 ^ dimHeight L.length

/-- **THE MEMORY TREE MATCHES THE STORAGE TREE.**  Over the same leaves, a memory run (eager and
lazy pushes in any order) and a storage run report the same `root()` and `height()`, and an eager
memory push returns the index and root the storage push returns. -/
def Properties.MemoryMatchesStorage : Prop :=
  ∀ (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256) (T : MemPushTree) (S : PushTree),
    MemRun h z depth L T → Run h z L S →
      (mRoot h T).map (·.2) = root S ∧ mHeight T = height S
        ∧ ∀ (x : UInt256) (T' : MemPushTree) (i : ℕ) (r : UInt256), mPush h T x = some (T', i, r) →
            ∃ S', push h S x = some (S', i, r)

/-- **THE RUN PREMISE IS SATISFIABLE, WITH THE LAZY BRANCH TAKEN.**  Three lazy pushes into a
depth-3 tree form a memory run whose last push left the flag set. -/
def Properties.LazyRunWitness : Prop :=
  ∀ (h : Hash) (z a b c : UInt256), ∃ T : MemPushTree,
    lazyRun h z 3 [a, b, c] = some T ∧ MemRun h z 3 [a, b, c] T ∧ T.needsRecalc = true

end Contracts.DynamicIncrementalMerkle
