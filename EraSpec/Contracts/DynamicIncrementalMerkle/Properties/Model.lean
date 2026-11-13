import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model

/-!
# Properties: `DynamicIncrementalMerkle` computes the full-tree root

Statements about `../Specs/Model.lean`, the transcription of
`DynamicIncrementalMerkle.sol` at `d9f678900e1bc8286412b78f56d4a9f443983c29`. Proofs are in
`../Proofs/Model.lean`. No statement takes a hash premise: each holds for every node hash `h`
and every padding value.

The library stores only one node per level (`_sides`), yet the root it returns is the root of
the full padded tree over every leaf pushed so far (`MerkleSpec.rootOf`, the fold `FullMerkle`
is specified against). The invariant is `Repr h z0 L H t`.

* **Calls.** `SetupRepresentsEmpty`, `PushComputesRoot`, `PushRevertsExactlyWhen`,
  `PushAccessInBounds`, `ExtendUntilEndRepresents`, `RootIsFold`.
* **Runs** (any interleaving of `setup`/`reset`/`clear`/`push`/`extendUntilEnd`).
  `ReachRepresents`, `ReachRootIsFold`, `PushNeverRevertsBelowMax`, `StepHeights`,
  `PushRunHeightIsMinimal`.
* **Proofs against the stored root.** `ReachHonestProofVerifies`,
  `ReachProofOpensLeafOrCollision`, `ReachProofAnyLengthOrBreak`,
  `ReachRootCommitsHistoryOrBreak`. The collisions are `MerkleSpec.Verifier.PathCollision` and
  `MerkleSpec.Pinned.TreeCollision`, located on the instance, never "some collision exists".
* **Countermodels and source remarks.** `WithoutGrowthRootForgetsLeaves`,
  `SecondSetupBreaksTheZeroCascade`, `EmptyRootIsZeroUntilExtended`.
* **Witness.** `ThreePushesWitness`.
-/

namespace Contracts.DynamicIncrementalMerkle

open Clear MerkleSpec MerkleSpec.Verifier MerkleSpec.Pinned

/-! ## Calls -/

/-- **`setup` ON BLANK STORAGE.** `setup(z)` on all-zero storage leaves a tree that
represents the empty leaf list at height 0. It returns `bytes32(0)`, and `root()` then reads
`bytes32(0)` and `height()` reads 0. -/
def Properties.SetupRepresentsEmpty : Prop :=
  ∀ (h : Hash) (z : UInt256),
    Repr h z [] 0 (setup blank z).1 ∧ (setup blank z).2 = 0
      ∧ root (setup blank z).1 = some 0 ∧ height (setup blank z).1 = some 0

/-- **`push` COMPUTES THE FULL-TREE ROOT.** From a tree representing `L` at height `H`, with
the counter below `type(uint256).max`, `push(x)` does not revert. It returns the index
`L.length` and the root of the full padded tree over `L ++ [x]` at the new height
`pushHeight L.length H` (one more than `H` exactly when `L.length == 1 << H`), and leaves a
tree representing `L ++ [x]` at that height. -/
def Properties.PushComputesRoot : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) (t : Tree) (x : UInt256),
    Repr h z0 L H t → L.length < UINT_MAX →
    ∃ t' : Tree,
      push h t x = some (t', L.length, rootOf h z0 (L ++ [x]) (pushHeight L.length H))
        ∧ Repr h z0 (L ++ [x]) (pushHeight L.length H) t'

/-- **WHEN `push` REVERTS.** For any storage (represented or not), `push` reverts exactly
when `_zeros` is empty (the `_zeros.length - 1` underflow, `:95`) or the counter is
`type(uint256).max` (`:99`). It has no capacity revert. -/
def Properties.PushRevertsExactlyWhen : Prop :=
  ∀ (h : Hash) (t : Tree) (x : UInt256),
    push h t x = none ↔ (t.zeros = [] ∨ t.next = UINT_MAX)

/-- **THE UNCHECKED ACCESSES OF `push` ARE IN BOUNDS.** On a tree representing `L` at height
`H`, after the growth block `levels` is `pushHeight L.length H` and both `_zeros` and `_sides`
have `levels + 1` entries. The loop (`:114-133`) touches `_sides[i]` and `_zeros[i]` only for
`i < levels`, and `:135` writes `_sides[levels]`, so every `Arrays.unsafeAccess` is inside
its array. -/
def Properties.PushAccessInBounds : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) (t : Tree),
    Repr h z0 L H t →
    (grow h t (t.zeros.length - 1) t.next).2.2 = pushHeight L.length H
      ∧ (grow h t (t.zeros.length - 1) t.next).1.length = pushHeight L.length H + 1
      ∧ (grow h t (t.zeros.length - 1) t.next).2.1.length = pushHeight L.length H + 1

/-- **`extendUntilEnd` KEEPS THE LEAVES AND RAISES THE HEIGHT.** From a tree representing `L`
at height `H`, `extendUntilEnd(d)` does not revert and leaves a tree representing the same
`L` at height `max H (d - 1)` (so `d` is the final length of `_sides`, one more than the
final `height()`). Afterwards `root()` is the full-tree root at that height, the empty tree
included. -/
def Properties.ExtendUntilEndRepresents : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) (t : Tree) (d : ℕ),
    Repr h z0 L H t →
    ∃ t' : Tree, extendUntilEnd h t d = some t' ∧ Repr h z0 L (max H (d - 1)) t'
      ∧ root t' = some (rootOf h z0 L (max H (d - 1)))
      ∧ height t' = some (max H (d - 1))

/-- **`root()` IS THE FOLD, `height()` IS THE HEIGHT.** On a tree representing a nonempty `L`
at height `H`, `root()` is `rootOf h z0 L H`. `height()` is `H`, and both arrays have `H + 1`
entries (not `H`, as the struct comment at `:28` says). -/
def Properties.RootIsFold : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) (t : Tree),
    Repr h z0 L H t →
    height t = some H ∧ t.sides.length = H + 1 ∧ t.zeros.length = H + 1
      ∧ (L ≠ [] → root t = some (rootOf h z0 L H))

/-! ## Runs -/

/-- **EVERY REACHABLE TREE REPRESENTS ITS HISTORY.** Along any sequence of successful
`setup` (on blank storage), `reset`, `clear`, `push` and `extendUntilEnd` calls: storage whose
ghost is `none` is blank, and storage whose ghost is `some (z, L)` represents exactly the
leaves `L` pushed since the last (re)set, with padding `z`, at some height. -/
def Properties.ReachRepresents : Prop :=
  ∀ (h : Hash) (t : Tree) (g : Option (UInt256 × List UInt256)), Reach h t g →
    (g = none → t = blank) ∧ (∀ z L, g = some (z, L) → ∃ H, Repr h z L H t)

/-- **THE ROOT AFTER `n` PUSHES IS THE FULL-TREE ROOT OF THE `n` LEAVES.** On every reachable
set-up tree, `height()` returns some `H` with `L.length ≤ 2^H`, the counter is `L.length`,
and if at least one leaf was pushed `root()` is `rootOf h z L H`: the root of the complete
binary tree of height `H` whose first `L.length` leaves are `L` and whose other leaves are
the padding `z`. -/
def Properties.ReachRootIsFold : Prop :=
  ∀ (h : Hash) (t : Tree) (z : UInt256) (L : List UInt256), Reach h t (some (z, L)) →
    ∃ H, height t = some H ∧ L.length ≤ 2 ^ H ∧ t.next = L.length
      ∧ (L ≠ [] → root t = some (rootOf h z L H))

/-- **`push` NEVER REVERTS ON A REACHABLE TREE BELOW THE COUNTER LIMIT.** It returns the
index `L.length` and a root, the new storage is reachable with `x` appended to the history,
and `root()` reads the returned root. -/
def Properties.PushNeverRevertsBelowMax : Prop :=
  ∀ (h : Hash) (t : Tree) (z : UInt256) (L : List UInt256) (x : UInt256),
    Reach h t (some (z, L)) → L.length < UINT_MAX →
    ∃ (t' : Tree) (r : UInt256), push h t x = some (t', L.length, r)
      ∧ Reach h t' (some (z, L ++ [x])) ∧ root t' = some r

/-- **HOW THE HEIGHT MOVES.** From a reachable set-up tree of height `H`: a successful `push`
gives height `pushHeight L.length H` (which is `H` or `H + 1`), and a successful
`extendUntilEnd(d)` gives `max H (d - 1)`. So the height never decreases except by
`reset`/`clear`. -/
def Properties.StepHeights : Prop :=
  ∀ (h : Hash) (t t' : Tree) (z : UInt256) (L : List UInt256) (H : ℕ),
    Reach h t (some (z, L)) → height t = some H →
    (∀ (x r : UInt256) (i : ℕ), push h t x = some (t', i, r) →
        height t' = some (pushHeight L.length H) ∧ H ≤ pushHeight L.length H
          ∧ pushHeight L.length H ≤ H + 1)
      ∧ (∀ d : ℕ, extendUntilEnd h t d = some t' → height t' = some (max H (d - 1)))

/-- **THE HEIGHT OF A PUSH-ONLY TREE IS THE LEAST THAT FITS.** After `setup` on blank
storage and `n` pushes (no `extendUntilEnd`), the storage is reachable, `height()` is the
least `H` with `n ≤ 2^H` (so 0 for `n ≤ 1`, then `⌈log₂ n⌉`), and for `n ≥ 1` `root()` is the
full-tree root at that height. -/
def Properties.PushRunHeightIsMinimal : Prop :=
  ∀ (h : Hash) (z : UInt256) (t : Tree) (L : List UInt256), PushRun h z t L →
    Reach h t (some (z, L))
      ∧ ∃ H, height t = some H ∧ L.length ≤ 2 ^ H ∧ (∀ H', L.length ≤ 2 ^ H' → H ≤ H')
          ∧ (L ≠ [] → root t = some (rootOf h z L H))

/-! ## Proofs against the stored root -/

/-- **THE HONEST PROOF VERIFIES.** On a reachable tree with at least one leaf, for every
index `j` below the capacity `2^H`: walking the tree's own siblings from the entry at `j`
(the pushed leaf if `j < L.length`, the padding `z` otherwise) gives `root()`, and that walk
has no `PathCollision`. -/
def Properties.ReachHonestProofVerifies : Prop :=
  ∀ (h : Hash) (t : Tree) (z : UInt256) (L : List UInt256), Reach h t (some (z, L)) → L ≠ [] →
    ∀ (H : ℕ) (R : UInt256), height t = some H → root t = some R →
    ∀ j, j < 2 ^ H →
      walkPure h (honestSibs h z L j) 0 H j (L.getD j z) = R
        ∧ ¬ PathCollision h z L (honestSibs h z L j) 0 H j (L.getD j z)

/-- **A PROOF OF THE TREE'S HEIGHT OPENS THE LEAF AT ITS INDEX, OR A PINNED COLLISION.** On a
reachable tree with at least one leaf, any sibling stream whose walk of length `height()`
from index `j < 2^H` and claimed leaf `x` gives `root()` satisfies one of:
* `j` is an occupied index and `x` is the leaf pushed at `j`;
* `j` is past the last leaf and `x` is the padding value `z`;
* a `PathCollision`: at a named step the verifier hashed a pair different from the tree's
  pair at that position, to the same value.
No hash premise. The second case is why the padding must not be a possible leaf. -/
def Properties.ReachProofOpensLeafOrCollision : Prop :=
  ∀ (h : Hash) (t : Tree) (z : UInt256) (L : List UInt256), Reach h t (some (z, L)) → L ≠ [] →
    ∀ (H : ℕ) (R : UInt256), height t = some H → root t = some R →
    ∀ (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256), j < 2 ^ H →
      walkPure h sibs 0 H j x = R →
      (j < L.length ∧ L.getD j z = x) ∨ (L.length ≤ j ∧ x = z)
        ∨ PathCollision h z L sibs 0 H j x

/-- **ANY PATH LENGTH.** The same for a walk of any length `k` (the verifier
`Merkle.calculateRoot` does not know the tree's height): the length is `height()` and the
walk opens the entry at `j`, or it collides on the submitted path at that length, or it is a
located `HeightBreak` (an interior node presented as a leaf, or a level-0 entry that is a
node hash of the verifier's own pair, or a collision on the re-anchored walk). -/
def Properties.ReachProofAnyLengthOrBreak : Prop :=
  ∀ (h : Hash) (t : Tree) (z : UInt256) (L : List UInt256), Reach h t (some (z, L)) → L ≠ [] →
    ∀ (H : ℕ) (R : UInt256), height t = some H → root t = some R →
    ∀ (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256), j < 2 ^ k →
      walkPure h sibs 0 k j x = R →
      (k = H ∧ L.getD j z = x) ∨ (k = H ∧ PathCollision h z L sibs 0 k j x)
        ∨ HeightBreak h z L sibs k H j x

/-- **THE ROOT COMMITS TO THE WHOLE HISTORY, OR A LOCATED BREAK.** Two reachable trees with
the same padding, the same height and the same root (each with at least one leaf) hold the
same leaf list, or one list holds the padding value at the other's length (`PaddingHit`),
or at an index where the lists differ the two trees hash different pairs to the same value
on that index's path (`TreeCollision`). In particular a later state of one run with the same
height and root as an earlier one pushed nothing but padding values in between. -/
def Properties.ReachRootCommitsHistoryOrBreak : Prop :=
  ∀ (h : Hash) (t₁ t₂ : Tree) (z : UInt256) (L₁ L₂ : List UInt256),
    Reach h t₁ (some (z, L₁)) → Reach h t₂ (some (z, L₂)) → L₁ ≠ [] → L₂ ≠ [] →
    ∀ (H : ℕ) (R : UInt256), height t₁ = some H → height t₂ = some H →
      root t₁ = some R → root t₂ = some R →
      L₁ = L₂ ∨ PaddingHit z L₁ L₂
        ∨ ∃ i < max L₁.length L₂.length,
            L₁.getD i z ≠ L₂.getD i z ∧ TreeCollision h z L₁ L₂ H i

/-! ## Countermodels and source remarks -/

/-- **COUNTERMODEL: THE GROWTH BLOCK IS LOAD-BEARING.** With `:102-108` deleted, `setup`,
`push(a)`, `push(b)` on blank storage ends with `root() = b` for every hash and every `a`:
the first leaf is not committed, so two different histories share a root with no collision
anywhere. With the block, the same calls end with `root() = h a b`. -/
def Properties.WithoutGrowthRootForgetsLeaves : Prop :=
  ∀ (h : Hash) (z a a' b : UInt256),
    twoPushesNoGrow h z a b = some b ∧ twoPushesNoGrow h z a' b = some b
      ∧ ∃ t₁ t₂ : Tree, push h (setup blank z).1 a = some (t₁, 0, a)
          ∧ push h t₁ b = some (t₂, 1, h a b) ∧ root t₂ = some (h a b)

/-- **`setup` ON A SET-UP TREE BREAKS THE ZERO CASCADE.** `setup(z)` then `setup(z')` on
blank storage gives a tree that reports height 1 with `_zeros = [z, z']`. Unless `z'`
happens to be `h z z`, it represents no leaf list under any padding at any height. This is
the call `Reach` leaves out; `reset` does `clear` first. -/
def Properties.SecondSetupBreaksTheZeroCascade : Prop :=
  ∀ (h : Hash) (z z' : UInt256),
    height (setup (setup blank z).1 z').1 = some 1
      ∧ (setup (setup blank z).1 z').1.zeros = [z, z']
      ∧ (z' ≠ h z z → ∀ (z0 : UInt256) (L : List UInt256) (H : ℕ),
            ¬ Repr h z0 L H (setup (setup blank z).1 z').1)

/-- **THE EMPTY TREE'S ROOT IS `bytes32(0)` UNTIL `extendUntilEnd`.** After `setup(z)` on
blank storage `root()` is `bytes32(0)`, while the full-tree root of no leaves at height 0 is
the padding `z`. `extendUntilEnd(d)` on that tree then makes `root()` the all-padding root
`zeros h z (d - 1)`; with `d ≤ 1` the height stays 0 and `root()` changes from `0` to `z`.
So `initialRoot` (`:53`, `:64`) is not the root of the empty padded tree unless `z = 0`. -/
def Properties.EmptyRootIsZeroUntilExtended : Prop :=
  ∀ (h : Hash) (z : UInt256),
    root (setup blank z).1 = some 0 ∧ rootOf h z [] 0 = z
      ∧ ∀ d : ℕ, ∃ t' : Tree, extendUntilEnd h (setup blank z).1 d = some t'
          ∧ root t' = some (zeros h z (d - 1)) ∧ height t' = some (d - 1)

/-! ## Witness -/

/-- **THE PREMISES ARE SATISFIABLE, WITH THE HEIGHT GROWING TWICE.** For every hash and
padding, `setup` and three pushes on blank storage succeed. The result is reachable (by a
push-only run), has counter 3 and height 2, and `root()` is `h (h a b) (h c z)`. -/
def Properties.ThreePushesWitness : Prop :=
  ∀ (h : Hash) (z a b c : UInt256), ∃ t : Tree,
    threePushes h z a b c = some t ∧ PushRun h z t [a, b, c] ∧ Reach h t (some (z, [a, b, c]))
      ∧ t.next = 3 ∧ height t = some 2 ∧ root t = some (h (h a b) (h c z))

end Contracts.DynamicIncrementalMerkle
