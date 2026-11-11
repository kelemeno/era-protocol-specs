import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model

/-!
# Properties: the storage `DynamicIncrementalMerkle` computes the fold at its minimal height

Statements about `EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model`, the transcription of
`DynamicIncrementalMerkle.sol`.  Proofs are in `EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.Model`.

The invariant is `Represents h z L H S`: `_nextLeafIndex = |L|`, `|L| ≤ 2^H`,
`_zeros[i] = zeros h z i` and `_sides` has `H + 1` entries; at each level `i < H` where bit `i` of
`|L|` is set, `_sides[i]` is the completed left node `frontierNode h z L i`; and the root slot
`_sides[H]` is `dimRoot h z L H` (`bytes32(0)` for the empty tree, `rootOf h z L H` otherwise).

* **(a) The empty tree.**  `setup` on fresh storage represents the empty tree at height 0 and
  returns `0`; its `root()` is `0`, which is not the fold `rootOf h z [] 0 = z` whenever the zero
  value is nonzero, as `CHAIN_TREE_EMPTY_ENTRY_HASH` is.
* **(b) `push`.**  From any representing storage, `push(x)` never reverts, returns the leaf's index
  and the fold over `L ++ [x]`, and grows the height by one exactly when `|L| = 2^H`.
* **(c) The sides.**  Along runs the saved sides are the completed left nodes; the fork's
  `updatedSides` write policy returns the same roots as OpenZeppelin's save-every-left-node policy
  (the stored `_sides` can differ); a guard without `isLeft` returns a wrong root after two
  pushes.
* **(d) Runs.**  Every storage reached by `setup(z)` and pushes represents its leaves at the
  minimal height `⌈log₂ |L|⌉`, and `root()` is the fold there (`0` while empty).
* **(e) `extendUntilEnd` and `reset`.**  Extending to depth `d` keeps the sides invariant at height
  `max H (d - 1)` and leaves the fold at that height in the root slot, for the empty tree too
  (where it replaces `0` by the zero cascade).  `reset` is `setup` on fresh storage.
* **Witnesses.**  The one-, two- and three-push runs, with the storage written out.

No hash premise is used anywhere: every statement holds for every node hash `h` and zero `z`.
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec

/-! ## (a) `setup` and the empty root -/

/-- **`setup` ESTABLISHES THE INVARIANT.**  On fresh storage `setup(z)` represents the empty tree
at height 0 and returns `bytes32(0)`. -/
def Properties.SetupRepresentsEmpty : Prop :=
  ∀ (h : Hash) (z : UInt256),
    Represents h z [] 0 (setup PushTree.empty z).1 ∧ (setup PushTree.empty z).2 = 0

/-- **THE EMPTY ROOT IS `bytes32(0)`.**  Every storage representing the empty tree reports root
`0` and, after `setup`, height `0`. -/
def Properties.DimEmptyRootIsZero : Prop :=
  ∀ (h : Hash) (z : UInt256),
    root (setup PushTree.empty z).1 = some 0 ∧ height (setup PushTree.empty z).1 = some 0
      ∧ ∀ (H : ℕ) (S : PushTree), Represents h z [] H S → root S = some 0

/-- **COUNTERMODEL: THE EMPTY ROOT IS NOT THE FOLD.**  For every hash and every nonzero zero
value `z`, the freshly set-up tree reports `0` while the fold over no leaves is `z`.  So
"the root is `rootOf h z leaves height`" is false for an empty chain tree. -/
def Properties.EmptyRootIsNotTheFold : Prop :=
  ∀ (h : Hash) (z : UInt256), z ≠ 0 →
    rootOf h z [] 0 = z ∧ root (setup PushTree.empty z).1 ≠ some (rootOf h z [] 0)

/-- **AT THE PIN'S CONSTANT.**  A `MessageRoot` chain tree right after `_addNewChain`'s
`setup(CHAIN_TREE_EMPTY_ENTRY_HASH)` (MessageRootBase.sol:350) reports root `0`, not the fold. -/
def Properties.ChainTreeEmptyRootIsNotTheFold : Prop :=
  ∀ h : Hash,
    root (setup PushTree.empty chainTreeEmptyEntryHash).1 = some 0
      ∧ root (setup PushTree.empty chainTreeEmptyEntryHash).1
          ≠ some (rootOf h chainTreeEmptyEntryHash [] 0)

/-! ## (b) `push` -/

/-- **`push` COMPUTES THE FOLD, GROWING EXACTLY WHEN FULL.**  From storage representing the tree
over `L` at height `H`, `push(x)` does not revert.  It returns index `|L|` and the fold over
`L ++ [x]` at the new height, which is `H + 1` when `|L| = 2^H` (the growth branch, :102-108) and
`H` otherwise, and the new storage represents `L ++ [x]` there. -/
def Properties.PushComputesRoot : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) (x : UInt256),
    Represents h z L H S →
    ∃ S' : PushTree,
      push h S x
          = some (S', L.length, rootOf h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H))
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S'

/-- **`push` AFTER `extendUntilEnd` COMPUTES THE FOLD TOO.**  The same from storage in the
extended form (root slot holding the fold even when empty). -/
def Properties.PushAfterExtendComputesRoot : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) (x : UInt256),
    ExtendedRepresents h z L H S →
    ∃ S' : PushTree,
      push h S x
          = some (S', L.length, rootOf h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H))
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S'

/-- **`push` BEFORE `setup` REVERTS.**  On storage whose `_zeros` is empty (fresh storage, or
after `clear`), `_zeros.length - 1` underflows. -/
def Properties.PushBeforeSetupReverts : Prop :=
  ∀ (h : Hash) (S : PushTree) (x : UInt256), S.zeros = [] → push h S x = none

/-! ## (c) The saved sides -/

/-- **THE SIDES INVARIANT ALONG RUNS.**  In storage reached by `setup(z)` and pushes of `L`, at
every level below the height where the next push arrives as a right child, `_sides[i]` is the
completed left node it will hash with. -/
def Properties.SidesInvariant : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree), Run h z L S →
    ∀ i, i < dimHeight L.length → L.length / 2 ^ i % 2 = 1 →
      S.sides.getD i 0 = frontierNode h z L i

/-- **THE `updatedSides` FORK RETURNS OPENZEPPELIN'S ROOTS.**  From any representing storage,
the deployed `push` and the same push under OpenZeppelin's policy (save every left node) return
the same index and root, and both leave storage representing `L ++ [x]` at the same height. -/
def Properties.OzEquivalent : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) (x : UInt256),
    Represents h z L H S →
    ∃ (S₁ S₂ : PushTree) (r : UInt256),
      push h S x = some (S₁, L.length, r) ∧ ozPush h S x = some (S₂, L.length, r)
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S₁
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S₂

/-- **…BUT NOT OPENZEPPELIN'S STORAGE.**  Five pushes from `setup` leave different `_sides` under
the two policies (the fork keeps the stale `h a b` at level 1 where OpenZeppelin saves
`h e z`), for some hash; the roots agree by `OzEquivalent`. -/
def Properties.OzSidesDiffer : Prop :=
  ∃ (h : Hash) (z a b c d e : UInt256) (S₁ S₂ : PushTree),
    pushAll h (setup PushTree.empty z).1 [a, b, c, d, e] = some S₁
      ∧ pushAllWith h false (setup PushTree.empty z).1 [a, b, c, d, e] = some S₂
      ∧ S₁.sides ≠ S₂.sides ∧ root S₁ = root S₂

/-- **COUNTERMODEL: A GUARD WITHOUT `isLeft` BREAKS THE ROOT.**  With `if (!updatedSides)` in
place of `if (isLeft && !updatedSides)`, the second push overwrites `_sides[0]` with the new leaf
before reading it as the left sibling: for every hash it returns `h b b`, and for some hash that
is not the fold `h a b`. -/
def Properties.MisplacedGuardBreaksRoot : Prop :=
  (∀ (h : Hash) (z a b : UInt256),
    ((misplacedPush h (setup PushTree.empty z).1 a).bind fun r => misplacedPush h r.1 b).map
        (·.2.2) = some (h b b))
    ∧ ∃ (h : Hash) (z a b : UInt256), h b b ≠ rootOf h z [a, b] 1

/-! ## (d) Runs: the minimal height and the stored root -/

/-- **EVERY RUN SITS AT THE MINIMAL HEIGHT.**  Storage reached by `setup(z)` and pushes of `L`
represents `L` at `dimHeight |L| = Nat.clog 2 |L|`, the least `H` with `|L| ≤ 2^H`. -/
def Properties.ReachableHeightMinimal : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree), Run h z L S →
    Represents h z L (dimHeight L.length) S ∧ height S = some (dimHeight L.length)
      ∧ ∀ H', L.length ≤ 2 ^ H' → dimHeight L.length ≤ H'

/-- **THE HEIGHT GROWS EXACTLY WHEN THE TREE IS FULL.**  `dimHeight (n + 1)` is
`dimHeight n + 1` when `n = 2^(dimHeight n)` and `dimHeight n` otherwise; this is the recursion
the growth branch (:102) runs. -/
def Properties.DimHeightSucc : Prop :=
  ∀ n : ℕ, dimHeight (n + 1) = if n = 2 ^ dimHeight n then dimHeight n + 1 else dimHeight n

/-- **`root()` IS THE FOLD.**  On representing storage, `_sides[_sides.length - 1]` is
`dimRoot h z L H`: `0` for the empty tree, `rootOf h z L H` otherwise. -/
def Properties.RootIsFold : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree),
    Represents h z L H S → root S = some (dimRoot h z L H) ∧ height S = some H

/-- **ALONG RUNS, `root()` IS THE FOLD AT THE MINIMAL HEIGHT.** -/
def Properties.RunRootIsFold : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree), Run h z L S →
    root S = some (dimRoot h z L (dimHeight L.length))

/-- **EVERY PUSH RETURNS THE STORED ROOT.**  From storage reached by a run, a successful `push(x)`
returns index `|L|` and the value `root()` reads afterwards. -/
def Properties.PushReturnsStoredRoot : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (S S' : PushTree) (x : UInt256) (i : ℕ)
    (r : UInt256), Run h z L S → push h S x = some (S', i, r) →
      i = L.length ∧ root S' = some r ∧ r = rootOf h z (L ++ [x]) (dimHeight (L.length + 1))

/-- **NO PUSH SEQUENCE REVERTS.**  From `setup(z)`, pushing any list of leaves succeeds, and the
result is the run over that list. -/
def Properties.PushAllSucceeds : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256),
    ∃ S : PushTree, pushAll h (setup PushTree.empty z).1 L = some S ∧ Run h z L S

/-! ## (e) `extendUntilEnd` and `reset` -/

/-- **`extendUntilEnd` LEAVES THE FOLD AT THE TARGET DEPTH.**  From storage representing `L` at
height `H` (with `H = 0` if the tree is empty, as on every run), `extendUntilEnd(d)` does not
revert and leaves storage in the extended form at height `max H (d - 1)`, whose `root()` is the
fold `rootOf h z L (max H (d - 1))`.  For the empty tree that is the zero cascade, no longer `0`. -/
def Properties.ExtendUntilEndRoot : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) (d : ℕ),
    Represents h z L H S → (L = [] → H = 0) →
    ∃ S' : PushTree, extendUntilEnd h S d = some S'
      ∧ ExtendedRepresents h z L (max H (d - 1)) S'
      ∧ root S' = some (rootOf h z L (max H (d - 1)))

/-- **EXTENDING AGAIN.**  The same from storage already in the extended form, at any height. -/
def Properties.ExtendUntilEndAgain : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) (d : ℕ),
    ExtendedRepresents h z L H S →
    ∃ S' : PushTree, extendUntilEnd h S d = some S'
      ∧ ExtendedRepresents h z L (max H (d - 1)) S'
      ∧ root S' = some (rootOf h z L (max H (d - 1)))

/-- **`reset` IS `setup` ON FRESH STORAGE**, from any storage, including its return value. -/
def Properties.ResetIsSetup : Prop :=
  ∀ (S : PushTree) (z : UInt256), reset S z = setup PushTree.empty z

/-! ## Witnesses: the one-, two- and three-push growth runs -/

/-- **ONE PUSH.**  The root is the leaf itself, at height 0; nothing is hashed. -/
def Properties.OnePushWitness : Prop :=
  ∀ (h : Hash) (z a : UInt256),
    pushAll h (setup PushTree.empty z).1 [a] = some ⟨1, [a], [z]⟩
      ∧ Run h z [a] ⟨1, [a], [z]⟩ ∧ root ⟨1, [a], [z]⟩ = some a

/-- **TWO PUSHES.**  The second push grows the tree to height 1. -/
def Properties.TwoPushWitness : Prop :=
  ∀ (h : Hash) (z a b : UInt256),
    pushAll h (setup PushTree.empty z).1 [a, b] = some ⟨2, [a, h a b], [z, h z z]⟩
      ∧ Run h z [a, b] ⟨2, [a, h a b], [z, h z z]⟩
      ∧ root ⟨2, [a, h a b], [z, h z z]⟩ = some (h a b)

/-- **THREE PUSHES.**  The third push grows the tree to height 2 and saves `c` at level 0; the
root is `h (h a b) (h c z)`. -/
def Properties.ThreePushWitness : Prop :=
  ∀ (h : Hash) (z a b c : UInt256),
    pushAll h (setup PushTree.empty z).1 [a, b, c]
        = some ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ Run h z [a, b, c] ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ root ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
          = some (h (h a b) (h c z))

end Contracts.DynamicIncrementalMerkle
