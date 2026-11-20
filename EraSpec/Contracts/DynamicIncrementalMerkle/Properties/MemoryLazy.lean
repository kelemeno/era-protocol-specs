import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.MemoryLazy
import EraSpec.Core.Headline

/-!
# Properties: the memory tree and its lazy push

Statements about `EraSpec.Contracts.DynamicIncrementalMerkle.Specs.MemoryLazy`, the transcription
of `DynamicIncrementalMerkleMemory.sol` at `b17415d20`.  Proofs are in
`EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.MemoryLazy`.

* **The empty chain tree.**  The chain tree `L2MessageRoot.getEmptyMultichainBatchRoot` builds,
  `createTree(1); setup(CHAIN_TREE_EMPTY_ENTRY_HASH)`, returns `0` from `setup` and reports
  `root()` `0`, the root a storage chain tree reports right after `_addNewChain`'s `setup`
  (`EmptyChainTreeRootsAgree`).
* **Pushes, eager and lazy.**  From a memory tree representing `L` at `H`, `_pushInner` reverts
  exactly when the tree is full and the allocation has no slot for a new level.  Otherwise it
  keeps the invariant at the new height and, unless it left the flag set (an eager push never
  does), returns the new fold (`MemPushComputesRoot`).  On a represented tree `root()` returns the
  fold, recomputing it when the flag is set (`MemRootIsFold`).
* **Runs.**  Along every run of eager and lazy pushes from `createTree(depth); setup(z)`, in any
  order, the tree represents its leaves at the minimal height and `root()` is the fold there, `0`
  while empty (`LazyRootRecalculated`).  The flag is set only on a nonempty tree that is not full
  (`LazyFlagMeansNotFull`), so the push that grows the tree finds the old root in the root slot,
  which becomes a side.  The memory tree reports the same `root()` and `height()` as the storage
  tree over the same leaves, and an eager memory push returns what the storage push returns
  (`MemoryMatchesStorage`).
* **Witnesses**, for every hash and zero value: three lazy pushes into a depth-3 tree leave the
  flag set, `root()` recomputes `h (h a b) (h c z)`, and an eager fourth push returns index 3 and
  `h (h a b) (h c d)` (`LazyRunWitness`); in a depth-1 tree a second push reverts, in a depth-2
  tree it returns `h a b` (`MemPushWitness`).

No hash premise is used: every statement holds for every node hash `h` and zero `z`.
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec

/-! ## The empty chain tree -/

/-- **THE EMPTY CHAIN TREE'S ROOT IS `bytes32(0)` IN BOTH LIBRARIES.**
`L2MessageRoot.getEmptyMultichainBatchRoot` (L2MessageRoot.sol:79-91) builds its chain tree with
`createTree(1); setup(CHAIN_TREE_EMPTY_ENTRY_HASH)` and hashes the value `setup` returns into the
chain-id leaf (:87-88).  That value is `0`, the tree represents the empty tree at height 0, and
its `root()` is `0`.  A storage chain tree right after `_addNewChain`'s `setup`
(MessageRootBase.sol:285) also reports `root()` `0`; `_addNewChain` hashes `bytes32(0)` into its
chain-id leaf (:287).  For every hash. -/
def Properties.EmptyChainTreeRootsAgree : Prop :=
  ∀ h : Hash, ∃ T : MemPushTree,
    msetup (createTree MemPushTree.fresh 1) chainTreeEmptyEntryHash = some (T, 0)
      ∧ MemRepresents h chainTreeEmptyEntryHash [] 0 T
      ∧ (mRoot h T).map (·.2) = some 0
      ∧ root (setup PushTree.empty chainTreeEmptyEntryHash).1 = some 0

/-! ## Pushes and `root()` -/

/-- **`setup` ESTABLISHES THE MEMORY INVARIANT.**  On a tree allocated with depth `≥ 1`, `setup`
succeeds, returns `0` and represents the empty tree at height 0; with depth `0` it reverts. -/
def Properties.MemSetupRepresentsEmpty : Prop :=
  ∀ (h : Hash) (z : UInt256) (depth : ℕ),
    (depth = 0 → msetup (createTree MemPushTree.fresh depth) z = none)
      ∧ (0 < depth → ∃ T, msetup (createTree MemPushTree.fresh depth) z = some (T, 0)
          ∧ MemRepresents h z [] 0 T)

/-- **AN EAGER OR LAZY PUSH KEEPS THE INVARIANT, AND REVERTS ONLY WHEN OUT OF ROOM.**  From a
memory tree representing `L` at `H`, `_pushInner(x, lazy)` reverts when the tree is full and the
allocation has no slot for the new level; otherwise it returns index `|L|`, represents
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

/-- **`root()` RETURNS THE FOLD.**  On a memory tree representing `L` at `H`, `root()` returns
`dimRoot h z L H` (recomputing it from the sides and `_lastLeafValue` when the flag is set), and
leaves the tree representing `L` at `H` with the flag clear. -/
def Properties.MemRootIsFold : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (T : MemPushTree),
    MemRepresents h z L H T →
    ∃ T', mRoot h T = some (T', dimRoot h z L H) ∧ MemRepresents h z L H T'
      ∧ T'.needsRecalc = false

/-! ## Runs -/

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

/-- **THE FLAG IS SET ONLY ON A NONEMPTY TREE THAT IS NOT FULL.**  So the push that grows the
tree finds the old root in the root slot it turns into a side. -/
def Properties.LazyFlagMeansNotFull : Prop :=
  ∀ (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256) (T : MemPushTree),
    MemRun h z depth L T → T.needsRecalc = true →
      L ≠ [] ∧ L.length < 2 ^ dimHeight L.length

/-- **THE MEMORY TREE MATCHES THE STORAGE TREE.**  Over the same leaves, a memory run (eager and
lazy pushes in any order) and a storage run report the same `root()` and `height()`, and an eager
memory push returns the index and root the storage push returns.

Premises, in plain words: any node hash and zero value; a memory tree reached by
`createTree(depth)`, `setup(z)` and eager or lazy pushes of `L`, and a storage tree reached by
`setup(z)` on fresh storage and pushes of the same `L` (the transcriptions of
`DynamicIncrementalMerkleMemory.sol` and `DynamicIncrementalMerkle.sol`, `MODEL-DIM`, which leaves
`extendUntilEnd` and `index` of the memory library out). -/
@[headline] def Properties.MemoryMatchesStorage : Prop :=
  ∀ (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256) (T : MemPushTree) (S : PushTree),
    MemRun h z depth L T → Run h z L S →
      (mRoot h T).map (·.2) = root S ∧ mHeight T = height S
        ∧ ∀ (x : UInt256) (T' : MemPushTree) (i : ℕ) (r : UInt256), mPush h T x = some (T', i, r) →
            ∃ S', push h S x = some (S', i, r)

/-! ## Witnesses -/

/-- **THE RUN PREMISE IS SATISFIABLE, WITH THE LAZY BRANCH TAKEN.**  Three lazy pushes into a
depth-3 tree form a memory run whose last push left the flag set; the tree represents `[a, b, c]`
at height 2.  `root()` recomputes `h (h a b) (h c z)`, the value `ThreePushWitness` gives for the
storage run over the same leaves, and an eager fourth push returns index 3 and
`h (h a b) (h c d)`, the value `FourthPushWitness` gives for the storage push. -/
@[witness] def Properties.LazyRunWitness : Prop :=
  ∀ (h : Hash) (z a b c d : UInt256), ∃ T : MemPushTree,
    lazyRun h z 3 [a, b, c] = some T ∧ MemRun h z 3 [a, b, c] T ∧ T.needsRecalc = true
      ∧ MemRepresents h z [a, b, c] 2 T
      ∧ (mRoot h T).map (·.2) = some (h (h a b) (h c z))
      ∧ (mPush h T d).map (·.2) = some (3, h (h a b) (h c d))

/-- **A MEMORY PUSH REVERTS EXACTLY WITHOUT ROOM.**  In a tree allocated with depth 1, after
`setup(z)` a first push returns index 0 and root `a` at height 0; a second push reverts, since
the tree is full (`1 = 2^0`) and the allocation has no slot for a second level.  With depth 2 the
second push grows the tree and returns index 1 and `h a b`. -/
def Properties.MemPushWitness : Prop :=
  ∀ (h : Hash) (z a b : UInt256), ∃ T₁ T₂ : MemPushTree,
    ((msetup (createTree MemPushTree.fresh 1) z).bind fun r => mPush h r.1 a) = some (T₁, 0, a)
      ∧ MemRepresents h z [a] 0 T₁ ∧ T₁.sides.length ≤ 0 + 1 ∧ mPush h T₁ b = none
      ∧ ((msetup (createTree MemPushTree.fresh 2) z).bind fun r => mPush h r.1 a)
          = some (T₂, 0, a)
      ∧ MemRepresents h z [a] 0 T₂ ∧ (mPush h T₂ b).map (·.2) = some (1, h a b)

end Contracts.DynamicIncrementalMerkle
