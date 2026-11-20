import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model
import EraSpec.Core.Headline

/-!
# Properties: the storage `DynamicIncrementalMerkle` computes the fold at its minimal height

Statements about `EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model`, the transcription of
`DynamicIncrementalMerkle.sol` at `b17415d20`.  Proofs are in
`EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.Model`.

The invariant is `Represents h z L H S`: `_nextLeafIndex = |L|`, `|L| ≤ 2^H`,
`_zeros[i] = zeros h z i` and `_sides` has `H + 1` entries; at each level `i < H` where bit `i` of
`|L|` is set, `_sides[i]` is the completed left node `frontierNode h z L i`; and the root slot
`_sides[H]` is `dimRoot h z L H` (`bytes32(0)` for the empty tree, `rootOf h z L H` otherwise).

* **(a) The empty tree.**  `setup` on fresh storage represents the empty tree at height 0 and
  returns `0`; its `root()` is `0`, which is not the fold `rootOf h z [] 0 = z` whenever the zero
  value is nonzero, as `CHAIN_TREE_EMPTY_ENTRY_HASH` is.  So reading a chain tree's `root()` as
  the fold is correct for nonempty trees only.
* **(b) `push`.**  From any representing storage, `push(x)` does not revert, returns the leaf's
  index and the fold over `L ++ [x]`, and grows the height by one exactly when `|L| = 2^H`.
  Before `setup` (and after `clear`) it reverts.
* **(c) The sides.**  Along runs the saved sides at the levels the next push reads are the
  completed left nodes.  From representing storage, the fork's `updatedSides` write policy
  returns the same index and root as OpenZeppelin's save-every-left-node policy, and both leave
  representing storage; the stored `_sides` can differ.  A mutation of the source that drops
  `isLeft` from the guard (not the deployed code) returns `h b b` for the second leaf, which for
  some hash is not the fold, so the guard's `isLeft` test is needed.
* **(d) Runs.**  Every storage reached by `setup(z)` and pushes represents its leaves at the
  minimal height `⌈log₂ |L|⌉` (`dimHeight`), `root()` is the fold there (`0` while empty), and
  every push along a run returns the root `root()` then reads.
* **(e) `extendUntilEnd` and `reset`.**  From representing storage (at height 0 if empty),
  `extendUntilEnd(d)` keeps the sides invariant at height `max H (d - 1)` and leaves the fold at
  that height in the root slot, for the empty tree too (where it replaces `0` by the zero
  cascade); a further `push` returns the fold.  `reset` is `setup` on fresh storage.
* **Witnesses**, with the storage written out, for every hash and zero value: the one-, two-,
  three- and four-push runs (the third grows the tree, the fourth does not and leaves a stale
  side), the empty tree extended to depth 3, the three-push run extended to depth 4 and pushed
  once more, and `push` after `clear`.

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

/-- **THE EMPTY ROOT IS `bytes32(0)`.**  After `setup` on fresh storage, `root()` is `0` and
`height()` is `0`; every storage representing the empty tree, at any height, reports root `0`. -/
def Properties.DimEmptyRootIsZero : Prop :=
  ∀ (h : Hash) (z : UInt256),
    root (setup PushTree.empty z).1 = some 0 ∧ height (setup PushTree.empty z).1 = some 0
      ∧ ∀ (H : ℕ) (S : PushTree), Represents h z [] H S → root S = some 0

/-- **THE EMPTY ROOT IS NOT THE FOLD.**  For every hash and every nonzero zero value `z`, the
freshly set-up tree (height 0) reports `0` while the fold over no leaves at height 0 is `z`.  So
"`root()` is `rootOf h z leaves height`" does not hold for an empty tree. -/
@[countermodel] def Properties.EmptyRootIsNotTheFold : Prop :=
  ∀ (h : Hash) (z : UInt256), z ≠ 0 →
    rootOf h z [] 0 = z ∧ root (setup PushTree.empty z).1 ≠ some (rootOf h z [] 0)

/-- **AT THE `MessageRoot`'S CONSTANT.**  A `MessageRoot` chain tree right after `_addNewChain`'s
`setup(CHAIN_TREE_EMPTY_ENTRY_HASH)` (MessageRootBase.sol:285) reports root `0`, not the fold,
for every hash. -/
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

/-- **`push` AFTER `extendUntilEnd` COMPUTES THE FOLD TOO.**  The same as `PushComputesRoot`,
from storage in the extended form (`ExtendedRepresents`: the root slot holds the fold even when
the tree is empty). -/
def Properties.PushAfterExtendComputesRoot : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) (x : UInt256),
    ExtendedRepresents h z L H S →
    ∃ S' : PushTree,
      push h S x
          = some (S', L.length, rootOf h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H))
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S'

/-- **`push` BEFORE `setup` REVERTS.**  On storage whose `_zeros` is empty (fresh storage, or
after `clear`), `_zeros.length - 1` underflows (:95). -/
def Properties.PushBeforeSetupReverts : Prop :=
  ∀ (h : Hash) (S : PushTree) (x : UInt256), S.zeros = [] → push h S x = none

/-- **`clear` EMPTIES `_zeros`, SO `push` REVERTS UNTIL THE NEXT `setup`.**  On any storage,
`clear` leaves `_zeros` empty (the premise of `PushBeforeSetupReverts`) and a `push` then
reverts. -/
def Properties.PushAfterClearReverts : Prop :=
  ∀ (h : Hash) (S : PushTree) (x : UInt256), (clear S).zeros = [] ∧ push h (clear S) x = none

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

/-- **…BUT NOT OPENZEPPELIN'S STORAGE.**  For some hash (the left projection) and leaves, five
pushes from `setup` succeed under both policies and leave different `_sides` (the fork still
holds `h a b` at level 1 where OpenZeppelin's policy writes `h e z`), while `root()` agrees. -/
def Properties.OzSidesDiffer : Prop :=
  ∃ (h : Hash) (z a b c d e : UInt256) (S₁ S₂ : PushTree),
    pushAll h (setup PushTree.empty z).1 [a, b, c, d, e] = some S₁
      ∧ pushAllWith h false (setup PushTree.empty z).1 [a, b, c, d, e] = some S₂
      ∧ S₁.sides ≠ S₂.sides ∧ root S₁ = root S₂

/-- **A GUARD WITHOUT `isLeft` WOULD CHANGE THE ROOT.**  A mutation of the source, not the
deployed code: with `if (!updatedSides)` in place of `if (isLeft && !updatedSides)`, the second
push overwrites `_sides[0]` with the new leaf before reading it as the left sibling.  For every
hash it returns `h b b`, and for some hash that is not the fold `rootOf h z [a, b] 1`. -/
def Properties.MisplacedGuardBreaksRoot : Prop :=
  (∀ (h : Hash) (z a b : UInt256),
    ((misplacedPush h (setup PushTree.empty z).1 a).bind fun r => misplacedPush h r.1 b).map
        (·.2.2) = some (h b b))
    ∧ ∃ (h : Hash) (z a b : UInt256), h b b ≠ rootOf h z [a, b] 1

/-! ## (d) Runs: the minimal height and the stored root -/

/-- **EVERY RUN SITS AT THE MINIMAL HEIGHT.**  Storage reached by `setup(z)` and pushes of `L`
represents `L` at `dimHeight |L| = Nat.clog 2 |L|`, its `height()` is that, and it is the least
`H` with `|L| ≤ 2^H`.

Premises, in plain words: as for `RunRootIsFold`: any node hash and zero value; storage reached by
`setup(z)` on fresh storage and `push`es of `L` (`MODEL-DIM`). -/
@[headline] def Properties.ReachableHeightMinimal : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree), Run h z L S →
    Represents h z L (dimHeight L.length) S ∧ height S = some (dimHeight L.length)
      ∧ ∀ H', L.length ≤ 2 ^ H' → dimHeight L.length ≤ H'

/-- **THE HEIGHT GROWS EXACTLY WHEN THE TREE IS FULL.**  `dimHeight (n + 1)` is
`dimHeight n + 1` when `n = 2^(dimHeight n)` and `dimHeight n` otherwise; this is the recursion
the growth branch (:102) runs. -/
def Properties.DimHeightSucc : Prop :=
  ∀ n : ℕ, dimHeight (n + 1) = if n = 2 ^ dimHeight n then dimHeight n + 1 else dimHeight n

/-- **`root()` IS THE FOLD.**  On representing storage, `_sides[_sides.length - 1]` is
`dimRoot h z L H`: `0` for the empty tree, `rootOf h z L H` otherwise; `height()` is `H`. -/
def Properties.RootIsFold : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree),
    Represents h z L H S → root S = some (dimRoot h z L H) ∧ height S = some H

/-- **ALONG RUNS, `root()` IS THE FOLD AT THE MINIMAL HEIGHT** (`0` while empty).

Premises, in plain words: any node hash `h` (`Merkle.efficientHash`) and zero value `z`; the
storage is reached from fresh storage by `setup(z)` and successful `push`es of the leaves `L` (the
transcription of `DynamicIncrementalMerkle.sol`, `MODEL-DIM`; no leaf-count bound is needed, see
the model boundary of `Specs/Model.lean`); storage written directly, as
`PriorityTree.initFromCommitment` does, is not a run. -/
@[headline] def Properties.RunRootIsFold : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree), Run h z L S →
    root S = some (dimRoot h z L (dimHeight L.length))

/-- **EVERY PUSH RETURNS THE STORED ROOT.**  From storage reached by a run, a successful `push(x)`
returns index `|L|` and the value `root()` reads afterwards, which is the fold over `L ++ [x]` at
`dimHeight (|L| + 1)`. -/
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

/-- **ALONG RUNS: `extendUntilEnd`, THEN `push`.**  From storage reached by `setup(z)` and pushes
of `L`, `extendUntilEnd(d)` does not revert and `root()` afterwards is the fold over `L` at
`H' = max (dimHeight |L|) (d - 1)`.  A further `push(x)` does not revert, returns index `|L|`
and the fold over `L ++ [x]` at `H' + 1` when `|L| = 2^H'` and at `H'` otherwise, and leaves
storage representing `L ++ [x]` at that height. -/
def Properties.RunExtendThenPush : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree) (d : ℕ) (x : UInt256),
    Run h z L S →
    ∃ S' S'' : PushTree, extendUntilEnd h S d = some S'
      ∧ root S' = some (rootOf h z L (max (dimHeight L.length) (d - 1)))
      ∧ push h S' x = some (S'', L.length,
          rootOf h z (L ++ [x])
            (if L.length = 2 ^ max (dimHeight L.length) (d - 1)
              then max (dimHeight L.length) (d - 1) + 1 else max (dimHeight L.length) (d - 1)))
      ∧ Represents h z (L ++ [x])
          (if L.length = 2 ^ max (dimHeight L.length) (d - 1)
            then max (dimHeight L.length) (d - 1) + 1 else max (dimHeight L.length) (d - 1)) S''

/-- **`reset` IS `setup` ON FRESH STORAGE**, from any storage, including its return value. -/
def Properties.ResetIsSetup : Prop :=
  ∀ (S : PushTree) (z : UInt256), reset S z = setup PushTree.empty z

/-! ## Witnesses, for every hash and zero value -/

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
root is `h (h a b) (h c z)`.  The storage is a run and represents `[a, b, c]` at height 2: bits
0 and 1 of 3 are set, and the sides there are the completed left nodes `c` and `h a b`. -/
@[witness] def Properties.ThreePushWitness : Prop :=
  ∀ (h : Hash) (z a b c : UInt256),
    pushAll h (setup PushTree.empty z).1 [a, b, c]
        = some ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ Run h z [a, b, c] ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ Represents h z [a, b, c] 2
          ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ frontierNode h z [a, b, c] 0 = c ∧ frontierNode h z [a, b, c] 1 = h a b
      ∧ root ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
          = some (h (h a b) (h c z))

/-- **A FOURTH PUSH, WITHOUT GROWTH.**  From the three-push storage, `push(d)` returns index 3
and `h (h a b) (h c d)`, the fold over `[a, b, c, d]` at height 2 (no growth: `3 ≠ 2^2`).  The
push's path turns right at both levels, so it writes only the root slot: `_sides[0]` keeps the
stale `c`, which the invariant does not constrain (bit 0 of 4 is clear).  The new storage is the
run over the four leaves, represents them at height 2, and its `root()` is the returned value. -/
def Properties.FourthPushWitness : Prop :=
  ∀ (h : Hash) (z a b c d : UInt256),
    push h ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩ d
        = some (⟨4, [c, h a b, h (h a b) (h c d)], [z, h z z, h (h z z) (h z z)]⟩, 3,
            h (h a b) (h c d))
      ∧ rootOf h z [a, b, c, d] 2 = h (h a b) (h c d)
      ∧ Run h z [a, b, c, d] ⟨4, [c, h a b, h (h a b) (h c d)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ Represents h z [a, b, c, d] 2
          ⟨4, [c, h a b, h (h a b) (h c d)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ root ⟨4, [c, h a b, h (h a b) (h c d)], [z, h z z, h (h z z) (h z z)]⟩
          = some (h (h a b) (h c d))

/-- **EXTENDING THE EMPTY TREE.**  On the freshly set-up tree, whose `root()` is `0`,
`extendUntilEnd(3)` writes `_sides[0] = z` and appends two levels of the zero cascade.  The result
is in the extended form for no leaves at height 2, and its `root()` is the fold there,
`h (h z z) (h z z)`. -/
def Properties.ExtendEmptyWitness : Prop :=
  ∀ (h : Hash) (z : UInt256),
    extendUntilEnd h (setup PushTree.empty z).1 3
        = some ⟨0, [z, h z z, h (h z z) (h z z)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ ExtendedRepresents h z [] 2
          ⟨0, [z, h z z, h (h z z) (h z z)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ root ⟨0, [z, h z z, h (h z z) (h z z)], [z, h z z, h (h z z) (h z z)]⟩
          = some (rootOf h z [] 2)
      ∧ rootOf h z [] 2 = h (h z z) (h z z)

/-- **EXTEND, THEN PUSH.**  After the three pushes, `extendUntilEnd(4)` appends one level: the zero
`h Z₂ Z₂` and the root slot `h R Z₂`, for the three-leaf root `R = h (h a b) (h c z)` and
`Z₂ = h (h z z) (h z z)`.  That storage is in the extended form for `[a, b, c]` at height 3.  A
fourth push then stays at height 3 (no growth: `3 ≠ 2^3`) and returns index 3 and
`h (h (h a b) (h c d)) Z₂`, which is the fold over `[a, b, c, d]` at height 3. -/
def Properties.ExtendThenPushWitness : Prop :=
  ∀ (h : Hash) (z a b c d : UInt256),
    ((pushAll h (setup PushTree.empty z).1 [a, b, c]).bind fun S => extendUntilEnd h S 4)
        = some ⟨3, [c, h a b, h (h a b) (h c z), h (h (h a b) (h c z)) (h (h z z) (h z z))],
            [z, h z z, h (h z z) (h z z), h (h (h z z) (h z z)) (h (h z z) (h z z))]⟩
      ∧ ExtendedRepresents h z [a, b, c] 3
          ⟨3, [c, h a b, h (h a b) (h c z), h (h (h a b) (h c z)) (h (h z z) (h z z))],
            [z, h z z, h (h z z) (h z z), h (h (h z z) (h z z)) (h (h z z) (h z z))]⟩
      ∧ (((pushAll h (setup PushTree.empty z).1 [a, b, c]).bind fun S => extendUntilEnd h S 4).bind
            fun S => push h S d).map (·.2)
          = some (3, h (h (h a b) (h c d)) (h (h z z) (h z z)))
      ∧ rootOf h z [a, b, c, d] 3 = h (h (h a b) (h c d)) (h (h z z) (h z z))

end Contracts.DynamicIncrementalMerkle
