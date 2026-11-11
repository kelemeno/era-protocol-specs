import EraSpec.Contracts.Merkle.Specs.RootForgeryPinned

/-!
# Properties: the global-injectivity Merkle results, restated with a located collision

No hash premise anywhere in this file.  Each statement is a vacuous original with its
`hinj : ∀ a b c d, h a b = h c d → a = c ∧ b = d` premise removed and the collision it was
hiding added as a disjunct, located by `../Specs/RootForgeryPinned.lean` (or by
`PathCollision`).  Proofs: `../Proofs/RootForgeryPinned.lean`.

## Which statement replaces which

Every result in the `global-hinj` rows of `ASSUMPTIONS.md` ("Results whose premises cannot
hold") now has a pinned replacement.  Originals with the same statement share one.

| Vacuous original (module) | Pinned replacement |
|---|---|
| `levelUp_inj` (FullMerkle `Model`) | `LevelUpInjOrCollision` |
| `levels_inj` (FullMerkle `Model`) | `LevelsInjOrCollision` |
| `rootOf_inj_of_h_inj`, `rootOf_inj_of_h_inj'` (FullMerkle `Model`), `rootOf_inj_of_h_inj_of_on` (FullMerkle `CachedHashInjectivity`) | `RootOfInjOrCollision`; without the equal-length premise `RootCommitsListOrBreak` (padding case pinned: `MerkleSpec.PinnedStrong.RootCommitsListOrBreakStrong`) |
| `capacity_ok_root_commits` (FullMerkle `TreeShape`) | `RootOfInjOrCollision` (same statement); with the capacity premise discharged by the run, `Contracts.InteropCommitmentTree.PublishedRootCommitsOrCollision`, and without the equal-length premise `…PublishedRootCommitsAnyLengthOrBreak` |
| `rootOf_append_inj` (FullMerkle `Model`), `no_append_forgery` (Merkle `RootForgery`) | `RootOfAppendInjOrCollision` |
| `rootOf_set_inj` (FullMerkle `Model`) | `RootOfSetInjOrCollision` |
| `walkPure_inj` (FullMerkle `Model`), `no_path_forgery` (Merkle `RootForgery`) | `WalkPureInjOrCollision` |
| `walk_pins_leaf_and_sibs` (Merkle `ProofSound`) | `MerkleSpec.Verifier.WalkPinsOrCollision` (existing) |
| `no_forged_walk` (Merkle `ProofSound`) | `NoForgedWalkOrCollision` |
| `walk_accept_pins_leaf_free_sibs` (Merkle `ProofSound`) | `WalkAcceptPinsLeafFreeSibsOrCollision` |
| `mem_of_rootOf_eq` (Merkle `RootBinding`) | `MemOfRootOfEqOrCollision` |
| `getD_of_rootOf_eq` (Merkle `RootBinding`), `no_false_inclusion` (Merkle `RootForgery`) | `GetDOfRootOfEqOrCollision` |
| `rootOf_ne_of_not_mem` (Merkle `RootBinding`) | `RootOfNeOfNotMemOrCollision` |
| `root_ne_of_leaf_ne` (Merkle `RootForgery`) | `RootNeOfLeafNeOrCollision` |
| `path_forgery_changes_walk` (Merkle `RootForgery`) | `PathForgeryChangesWalkOrCollision` |
| `walk_accept_pins_leaf` (Merkle `RootForgery`) | `WalkAcceptPinsLeafOrCollision` |
| `leaf_only_substitution_changes_root` (Merkle `RootForgery`) | `LeafOnlySubstitutionChangesRootOrCollision` |
| `single_sibling_substitution` (Merkle `RootForgery`) | `SingleSiblingSubstitutionOrCollision`; any number of levels: `WalkVsWalkOrCollision` |
| `no_append_forgery_walk` (Merkle `RootForgery`) | `NoAppendForgeryWalkOrCollision` |
| `AcceptPinsEntry` (Merkle `Verifier`) | `AcceptPinsEntryOrCollision` (existing) |
| `AcceptPinsEntryCases` (Merkle `Verifier`) | `AcceptPinsEntryCasesOrCollision` |
| `AcceptForcesHeight`, `AcceptPinsEntryAnyLength` (Merkle `Verifier`) | `AcceptForcesHeightOrBreak`, `AcceptPinsEntryAnyLengthOrBreak` (existing) |

Each replacement keeps its original's premises, minus `hinj`, unless its docstring says a
premise was dropped (always because the proof does not need it, so the replacement is
stronger).

## Evidence that the replacements say something

* Each `…Satisfiable` witness names an instance meeting every premise of its property on
  which the located collision is FALSE, so the property is not vacuous and its collision
  disjunct is not implied by its premises.  Every `UInt256` hash collides somewhere
  (`exists_pair_collision`), so an unpinned "…or some collision exists" would hold on each
  of these instances; the pinned one does not.
* `EqualInstancesNeverCollide`: each located collision is false whenever the two sides are
  equal, for every hash.
* `RootPinsEntryPinnedToPath`: under `constHash` (every pair collides), on the same two trees,
  the collision is located on one index's path and is absent from another's.
* `PinnedFormsFire`, with `RootCommitsListCollisionFires` and `PaddingHitFires` for lists of
  different lengths: for every property in this file that has a collision disjunct (the 20
  replacements and the two engines), an instance meeting its premises on which the rest of
  its conclusion (for a replacement, the vacuous original's conclusion) is false, and the
  located collision (in `PaddingHitFires`, the padding hit) is what holds there.  The
  docstring of `PinnedFormsFire` names the case and the instance for each.
* `PaddingHitFires`: for every hash, the padding-ambiguity attack (`[a]` vs `[a, z0]`, the
  instance `TreeShape.padding_ambiguity_forges_root` is proved with) is located as exactly a
  `PaddingHit`, with no collision; `RootCommitsListCollisionFires` reaches the collision case
  alone, at different lengths and with the padding constant in neither list.  A `PaddingHit` can
  also hold ALONGSIDE a collision at an occupied index (`[1]` vs `[2, 0]` under `constHash`), so
  `RootCommitsListOrBreak`'s padding disjunct does not exclude one;
  `MerkleSpec.PinnedStrong.Properties.RootCommitsListOrBreakStrong`
  (`./RootForgeryPinnedStrong.lean`) restricts that case to lists agreeing at every padded entry.
* `WalkVsWalkNeedsSameIndex`: the same-index premise of `WalkVsWalkOrCollision` cannot be
  dropped.

At the commitment tree's own `_height`, where the run discharges the capacity premise, the
root-commitment form is `Contracts.InteropCommitmentTree.Properties.PublishedRootCommitsOrCollision`,
and for an attacker list of any length within capacity
`Contracts.InteropCommitmentTree.Properties.PublishedRootCommitsAnyLengthOrBreak`
(`../../L2InteropCommitmentTree/Properties/PublishedRootCommits.lean`).
-/

namespace MerkleSpec.Pinned

open Clear MerkleSpec MerkleSpec.Verifier

/-! ## The two engines -/

/-- **TREE VERSUS TREE: EQUAL ROOTS PIN EVERY COMMITTED ENTRY, OR A COLLISION ON ITS PATH.**
Two leaf lists whose roots at `height` are equal agree at every index `i < 2^height` (padding
included: `getD` with the padding constant), or the two trees hash different pairs to the
same value at a named level of `i`'s path.  No length, capacity or hash premise: a list
longer than `2^height` has entries its root does not commit, and `i < 2^height` says which
entries it does.  The tree-versus-tree counterpart of `AcceptPinsEntryOrCollision`. -/
def Properties.RootPinsEntryOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height i : ℕ),
    i < 2 ^ height → rootOf h z0 L₁ height = rootOf h z0 L₂ height →
      L₁.getD i z0 = L₂.getD i z0 ∨ TreeCollision h z0 L₁ L₂ height i

/-- **WALK VERSUS WALK: EQUAL RESULTS PIN THE LEAF AND EVERY CLIMBED SIBLING, OR A COLLISION.**
Two walks of the same length from the same level and index (any two leaves, any two sibling
streams) that reach the same value used the same leaf and the same sibling at every level they
climbed, or they hash different pairs to the same value at a named step.

This corrects the "HONEST LIMITATION (walk-vs-walk)" paragraph of `RootForgery`'s header,
which says pair-injectivity cannot rule out a compensating change to two or more sibling
levels of a walk.  For walks from the same index it can: peeling the last combine forces both
the accumulator and the sibling, level by level, exactly as against a tree root, so under
`hinj` the collision disjunct is impossible.  From different indices the compensation is real
and needs no collision (`WalkVsWalkNeedsSameIndex`). -/
def Properties.WalkVsWalkOrCollision : Prop :=
  ∀ (h : Hash) (s₁ s₂ : ℕ → UInt256) (k lvl j : ℕ) (x y : UInt256),
    walkPure h s₁ lvl k j x = walkPure h s₂ lvl k j y →
      (x = y ∧ ∀ l, lvl ≤ l → l < lvl + k → s₁ l = s₂ l) ∨ WalkCollision h s₁ s₂ lvl k j x y

/-- **THE SAME INDEX IS NEEDED.**  `WalkVsWalkOrCollision` compares two walks of the same length
from the same index.  From index 0 with leaf `x` and sibling `y`, and from index 1 with leaf `y`
and sibling `x`, two one-step walks hash the same pair `(x, y)`: they reach the same value under
EVERY hash, with different leaves and different siblings, and no collision is involved.  (A
prover chooses `calculateRootMemory`'s `_index` argument,
`l1-contracts/contracts/common/libraries/Merkle.sol:55`; against a tree root,
`AcceptPinsEntryOrCollision` pins the entry at whichever index is claimed.) -/
def Properties.WalkVsWalkNeedsSameIndex : Prop :=
  ∀ (h : Hash) (x y : UInt256),
    walkPure h (fun _ => y) 0 1 0 x = walkPure h (fun _ => x) 0 1 1 y

/-! ## FullMerkle `Model`, `CachedHashInjectivity`, `TreeShape` -/

/-- **`levelUp_inj`, PINNED.**  Two equal-width levels with the same parent level are equal,
or under some parent the two levels' child pairs differ and hash equal. -/
def Properties.LevelUpInjOrCollision : Prop :=
  ∀ (h : Hash) (z : UInt256) (L₁ L₂ : List UInt256),
    L₁.length = L₂.length → levelUp h z L₁ = levelUp h z L₂ →
      L₁ = L₂ ∨ LevelCollision h z L₁ L₂

/-- **`levels_inj`, PINNED.**  Equal-length leaf lists whose level-`l` lists coincide are equal,
or some level below `l` of the two trees collides under `levelUp`. -/
def Properties.LevelsInjOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (l : ℕ),
    L₁.length = L₂.length → levels h z0 L₁ l = levels h z0 L₂ l →
      L₁ = L₂ ∨ ∃ l' < l, LevelCollision h (zeros h z0 l') (levels h z0 L₁ l') (levels h z0 L₂ l')

/-- **`rootOf_inj_of_h_inj`, PINNED (also `rootOf_inj_of_h_inj'`, `rootOf_inj_of_h_inj_of_on`,
`capacity_ok_root_commits`, which have this statement).**  Equal-length leaf lists within
capacity with the same root are equal, or at an index where they differ the two trees collide
on that index's path.  (`hne` of `rootOf_inj_of_h_inj` is spurious and not taken.) -/
def Properties.RootOfInjOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    L₁.length = L₂.length → L₁.length ≤ 2 ^ height →
    rootOf h z0 L₁ height = rootOf h z0 L₂ height →
      L₁ = L₂ ∨ ∃ i < L₁.length, L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i

/-- **`rootOf_append_inj` / `no_append_forgery`, PINNED.**  Appending `x` or `y` at the same
frontier of a tree within capacity gives the same root only if `x = y`, or the two trees
collide on the path of the appended index `leaves.length`. -/
def Properties.RootOfAppendInjOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (x y : UInt256) (height : ℕ),
    (leaves ++ [x]).length ≤ 2 ^ height →
    rootOf h z0 (leaves ++ [x]) height = rootOf h z0 (leaves ++ [y]) height →
      x = y ∨ TreeCollision h z0 (leaves ++ [x]) (leaves ++ [y]) height leaves.length

/-- **`rootOf_set_inj`, PINNED.**  Overwriting leaf `idx` with `x` or with `y` gives the same
root only if `x = y`, or the two trees collide on the path of `idx`. -/
def Properties.RootOfSetInjOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (idx : ℕ) (x y : UInt256) (height : ℕ),
    idx < leaves.length → leaves.length ≤ 2 ^ height →
    rootOf h z0 (leaves.set idx x) height = rootOf h z0 (leaves.set idx y) height →
      x = y ∨ TreeCollision h z0 (leaves.set idx x) (leaves.set idx y) height idx

/-- **`walkPure_inj` / `no_path_forgery`, PINNED.**  Two leaves walked up the same sibling
stream from the same index reach the same value only if they are equal, or the two walks
collide at a named step. -/
def Properties.WalkPureInjOrCollision : Prop :=
  ∀ (h : Hash) (sibs : ℕ → UInt256) (k lvl idx : ℕ) (x y : UInt256),
    walkPure h sibs lvl k idx x = walkPure h sibs lvl k idx y →
      x = y ∨ WalkCollision h sibs sibs lvl k idx x y

/-- **ROOT BINDING WITH NO EQUAL-LENGTH PREMISE.**  Two leaf lists within capacity with the
same root are equal, or one holds the padding constant as a real leaf at the other's frontier
(`PaddingHit`), or at an index where they differ the trees collide on its path.

The equal-length premise of `rootOf_inj_of_h_inj` is load-bearing (`PaddingHitFires`, and
`TreeShapeStrong.padding_ambiguity_forges_root_pinned`); the padding ambiguity it excluded is a
domain case, not a cryptographic one, reached for every hash.  But `PaddingHit` reads only the
two lengths and the longer list's entry at the shorter one's length, so the second disjunct does
not say the lists agree anywhere else.  It also holds for pairs that differ at an index both
lists occupy, with a real collision there that this statement does not name (`[1]` and `[2, 0]`
under `constHash`: `MerkleSpec.PinnedStrong.Properties.RootCommitsListOrBreakStrongUnmasksCollision`).
The statement whose padding case is exactly the domain case (the lists agree at every padded
entry, one being the other followed by padding leaves) is
`MerkleSpec.PinnedStrong.Properties.RootCommitsListOrBreakStrong`. -/
def Properties.RootCommitsListOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    L₁.length ≤ 2 ^ height → L₂.length ≤ 2 ^ height →
    rootOf h z0 L₁ height = rootOf h z0 L₂ height →
      L₁ = L₂ ∨ PaddingHit z0 L₁ L₂
        ∨ ∃ i < max L₁.length L₂.length,
            L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i

/-- **ROOT BINDING UNDER THE INSTANCE'S OWN PADDING SEPARATION.**  If the padding constant is
not one of the two lists' leaves (what `FullMerkle.setup` asks of its `zero`,
`FullMerkle.sol:25-26`, here required only of these two lists), equal roots within capacity
give equal lists or a located collision, with no length premise. -/
def Properties.RootCommitsListUnderPadSeparation : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    z0 ∉ L₁ → z0 ∉ L₂ → L₁.length ≤ 2 ^ height → L₂.length ≤ 2 ^ height →
    rootOf h z0 L₁ height = rootOf h z0 L₂ height →
      L₁ = L₂ ∨ ∃ i < max L₁.length L₂.length,
        L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i

/-! ## Merkle `ProofSound`

`walk_pins_leaf_and_sibs` is replaced by the existing `MerkleSpec.Verifier.WalkPinsOrCollision`
(which also drops its range premise). -/

/-- **`no_forged_walk`, PINNED.**  If the tree's level-`lvl` entry at `j` is not `x`, then any
sibling stream that walks `x` up to the tree's node above `j` exhibits a `PathCollision` on
that path.  (The original's range premise `j < (levels h z0 L lvl).length` is not needed.) -/
def Properties.NoForgedWalkOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (k lvl j : ℕ) (x : UInt256),
    (levels h z0 L lvl).getD j (zeros h z0 lvl) ≠ x →
    ∀ sibs : ℕ → UInt256,
      walkPure h sibs lvl k j x = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k)) →
        PathCollision h z0 L sibs lvl k j x

/-- **`walk_accept_pins_leaf_free_sibs`, PINNED.**  A walk with attacker-chosen siblings from
an index `j < 2^height`, accepted against the root at `height`, used the tree's leaf at `j`
and the tree's sibling at every level, or it exhibits a `PathCollision` on the submitted path.
(The original's premises `j < L.length`, `L.length ≠ 0`, `L.length ≤ 2^height` are replaced
by the weaker `j < 2^height`, which they imply.) -/
def Properties.WalkAcceptPinsLeafFreeSibsOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ)
    (x : UInt256),
    j < 2 ^ height → walkPure h sibs 0 height j x = rootOf h z0 L height →
      (L.getD j z0 = x
        ∧ ∀ l, l < height → sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l))
      ∨ PathCollision h z0 L sibs 0 height j x

/-! ## Merkle `RootBinding` -/

/-- **`mem_of_rootOf_eq`, PINNED.**  A leaf `x` of one of two equal-length lists within
capacity with the same root is a leaf of the other, or the trees collide on the path of the
first position of `x` in the first list (`L₁.idxOf x`). -/
def Properties.MemOfRootOfEqOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ) (x : UInt256),
    L₁.length = L₂.length → L₁.length ≤ 2 ^ height →
    rootOf h z0 L₁ height = rootOf h z0 L₂ height → x ∈ L₁ →
      x ∈ L₂ ∨ TreeCollision h z0 L₁ L₂ height (L₁.idxOf x)

/-- **`getD_of_rootOf_eq` / `no_false_inclusion`, PINNED.**  Equal-length lists within capacity
with the same root agree at every index (any `getD` default), or the trees collide on that
index's path. -/
def Properties.GetDOfRootOfEqOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    L₁.length = L₂.length → L₁.length ≤ 2 ^ height →
    rootOf h z0 L₁ height = rootOf h z0 L₂ height →
      ∀ (i : ℕ) (d : UInt256), L₁.getD i d = L₂.getD i d ∨ TreeCollision h z0 L₁ L₂ height i

/-- **`rootOf_ne_of_not_mem`, PINNED.**  If `x` is a leaf of `L₁` and not of `L₂` (equal
lengths, within capacity), the roots differ, or the trees collide on the path of `L₁.idxOf x`. -/
def Properties.RootOfNeOfNotMemOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ) (x : UInt256),
    L₁.length = L₂.length → L₁.length ≤ 2 ^ height → x ∈ L₁ → x ∉ L₂ →
      rootOf h z0 L₁ height ≠ rootOf h z0 L₂ height
        ∨ TreeCollision h z0 L₁ L₂ height (L₁.idxOf x)

/-! ## Merkle `RootForgery`

`no_false_inclusion` is `GetDOfRootOfEqOrCollision`, `no_path_forgery` is
`WalkPureInjOrCollision`, and `no_append_forgery` is `RootOfAppendInjOrCollision`. -/

/-- **`root_ne_of_leaf_ne`, PINNED.**  Equal-length lists within capacity that differ at index
`i` have different roots, or the trees collide on `i`'s path. -/
def Properties.RootNeOfLeafNeOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height i : ℕ) (d : UInt256),
    L₁.length = L₂.length → L₁.length ≤ 2 ^ height → L₁.getD i d ≠ L₂.getD i d →
      rootOf h z0 L₁ height ≠ rootOf h z0 L₂ height ∨ TreeCollision h z0 L₁ L₂ height i

/-- **`path_forgery_changes_walk`, PINNED.**  Two distinct leaves walked up the same siblings
from the same index reach different values, or the walks collide at a named step. -/
def Properties.PathForgeryChangesWalkOrCollision : Prop :=
  ∀ (h : Hash) (sibs : ℕ → UInt256) (k lvl idx : ℕ) (x y : UInt256), x ≠ y →
    walkPure h sibs lvl k idx x ≠ walkPure h sibs lvl k idx y
      ∨ WalkCollision h sibs sibs lvl k idx x y

/-- **`walk_accept_pins_leaf`, PINNED.**  With the honest pre-update siblings (what
`FullMerkle.updateLeaf` reads, `FullMerkle.sol:82-87`), an accepted walk of `x` from `idx`
against `root` means `root` is the recomputed root of `leaves.set idx x` (no hash premise was
ever needed for this half), and any other leaf `y` accepted against the same root is `x`, or
its walk collides with `x`'s at a named step. -/
def Properties.WalkAcceptPinsLeafOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256) (leaves : List UInt256) (idx : ℕ)
    (x : UInt256) (height : ℕ) (root : UInt256),
    idx < leaves.length → leaves.length ≤ 2 ^ height →
    (∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (idx / 2 ^ l)) (zeros h z0 l)) →
    walkPure h sibs 0 height idx x = root →
      rootOf h z0 (leaves.set idx x) height = root
        ∧ ∀ y : UInt256, walkPure h sibs 0 height idx y = root →
            y = x ∨ WalkCollision h sibs sibs 0 height idx y x

/-- **`leaf_only_substitution_changes_root`, PINNED.**  Changing only the leaf at `idx` (all
siblings kept) changes the walk, or the two walks collide; and it changes the recomputed root
of the updated tree, or the two updated trees collide on `idx`'s path. -/
def Properties.LeafOnlySubstitutionChangesRootOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256) (leaves : List UInt256) (idx : ℕ)
    (x y : UInt256) (height : ℕ),
    idx < leaves.length → leaves.length ≤ 2 ^ height → x ≠ y →
      (walkPure h sibs 0 height idx x ≠ walkPure h sibs 0 height idx y
          ∨ WalkCollision h sibs sibs 0 height idx x y)
      ∧ (rootOf h z0 (leaves.set idx x) height ≠ rootOf h z0 (leaves.set idx y) height
          ∨ TreeCollision h z0 (leaves.set idx x) (leaves.set idx y) height idx)

/-- **`single_sibling_substitution`, PINNED.**  Two sibling streams agreeing off one climbed
level `m`, under which the same leaf reaches the same value, agree at `m` too, or the walks
collide at a named step.  (The agreement premise is kept from the original but not needed:
`WalkVsWalkOrCollision` handles any number of changed levels.) -/
def Properties.SingleSiblingSubstitutionOrCollision : Prop :=
  ∀ (h : Hash) (s₁ s₂ : ℕ → UInt256) (k lvl m idx : ℕ) (x : UInt256),
    lvl ≤ m → m < lvl + k → (∀ l, l ≠ m → s₁ l = s₂ l) →
    walkPure h s₁ lvl k idx x = walkPure h s₂ lvl k idx x →
      s₁ m = s₂ m ∨ WalkCollision h s₁ s₂ lvl k idx x x

/-- **`no_append_forgery_walk`, PINNED.**  With the honest frontier siblings (what
`FullMerkle.pushNewLeaf` → `updateLeaf` reads at the new index, `FullMerkle.sol:65, 82-87`),
a walk of `y` from the frontier index that reaches the honest root of `leaves ++ [x]` has
`y = x`, or its walk collides with `x`'s at a named step. -/
def Properties.NoAppendForgeryWalkOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256) (leaves : List UInt256) (x y : UInt256)
    (height : ℕ),
    leaves.length < 2 ^ height →
    (∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (leaves.length / 2 ^ l)) (zeros h z0 l)) →
    walkPure h sibs 0 height leaves.length y = rootOf h z0 (leaves ++ [x]) height →
      y = x ∨ WalkCollision h sibs sibs 0 height leaves.length y x

/-! ## Merkle `Verifier`

`AcceptPinsEntry`, `AcceptForcesHeight` and `AcceptPinsEntryAnyLength` are replaced by the
existing `AcceptPinsEntryOrCollision`, `AcceptForcesHeightOrBreak` and
`AcceptPinsEntryAnyLengthOrBreak`. -/

/-- **`AcceptPinsEntryCases`, PINNED.**  A walk of length `k` from `j < 2^k`, accepted against
the root at height `k`, opens an occupied index holding its leaf, or a padded index with the
padding constant as its leaf, or exhibits a `PathCollision` on the submitted path. -/
def Properties.AcceptPinsEntryCasesOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256),
    j < 2 ^ k → walkPure h sibs 0 k j x = rootOf h z0 L k →
      (j < L.length ∧ L.getD j z0 = x) ∨ (L.length ≤ j ∧ x = z0)
        ∨ PathCollision h z0 L sibs 0 k j x

/-! ## Each located collision is pinned to the instance -/

/-- **EQUAL SIDES NEVER COLLIDE, FOR EVERY HASH.**  A tree compared with itself, a walk with
itself, a level with itself: no located collision, and no padding hit. -/
def Properties.EqualInstancesNeverCollide : Prop :=
  (∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (height i : ℕ), ¬ TreeCollision h z0 L L height i)
  ∧ (∀ (h : Hash) (s : ℕ → UInt256) (lvl k j : ℕ) (x : UInt256), ¬ WalkCollision h s s lvl k j x x)
  ∧ (∀ (h : Hash) (z : UInt256) (L : List UInt256), ¬ LevelCollision h z L L)
  ∧ (∀ (z0 : UInt256) (L : List UInt256), ¬ PaddingHit z0 L L)

/-- **A PADDING HIT NEEDS A LEAF EQUAL TO THE PADDING CONSTANT.**  So it is excluded by the
instance's own padding separation, as in `RootCommitsListUnderPadSeparation`. -/
def Properties.PaddingHitNeedsPaddingLeaf : Prop :=
  ∀ (z0 : UInt256) (L₁ L₂ : List UInt256), PaddingHit z0 L₁ L₂ → z0 ∈ L₁ ∨ z0 ∈ L₂

/-- **THE TREE COLLISION IS PINNED TO A PATH.**  Under `constHash`, for which every pair
collides, the different trees `[1, 0, 5, 5]` and `[0, 1, 5, 5]` have the same root at height 2.
They differ at index 0, and the collision is located on index 0's path; they agree at index 2,
and no collision is located on index 2's path, though the trees and the hash are the same. -/
def Properties.RootPinsEntryPinnedToPath : Prop :=
  rootOf constHash 0 [1, 0, 5, 5] 2 = rootOf constHash 0 [0, 1, 5, 5] 2
    ∧ ([1, 0, 5, 5] : List UInt256).getD 0 0 ≠ ([0, 1, 5, 5] : List UInt256).getD 0 0
    ∧ TreeCollision constHash 0 [1, 0, 5, 5] [0, 1, 5, 5] 2 0
    ∧ ([1, 0, 5, 5] : List UInt256).getD 2 0 = ([0, 1, 5, 5] : List UInt256).getD 2 0
    ∧ ¬ TreeCollision constHash 0 [1, 0, 5, 5] [0, 1, 5, 5] 2 2

/-- **WITHOUT `hinj` EACH ORIGINAL CONCLUSION FAILS, AND THE LOCATED COLLISION IS WHAT HOLDS.**
Each case is an instance meeting the premises of the properties it names, on which the rest of
the property's conclusion (for a replacement, the vacuous original's conclusion; for the
engines `RootPinsEntryOrCollision` and `WalkVsWalkOrCollision`, their first disjunct) is
false.  The conjuncts state the premises that are not evident from the literals (lengths and
index bounds are), the failure, and the located collision.  Under `constHash` with
padding `0`:

1. tree versus tree: `[1]` and `[0]` (equal length, within capacity at height 1) have the same
   root, yet differ; the collision is on index 0's path.  Properties: `RootPinsEntryOrCollision`
   (`i = 0`), `RootOfInjOrCollision`, `RootCommitsListOrBreak` (no padding hit at equal
   lengths), `RootOfAppendInjOrCollision` (`leaves = []`, `x = 1`, `y = 0`),
   `RootOfSetInjOrCollision` and the root half of `LeafOnlySubstitutionChangesRootOrCollision`
   (`leaves = [7]`, `idx = 0`, `x = 1`, `y = 0`: `[7].set 0 1 = [1]`),
   `MemOfRootOfEqOrCollision` and `RootOfNeOfNotMemOrCollision` (`x = 1`, so `L₁.idxOf x = 0`),
   `GetDOfRootOfEqOrCollision` and `RootNeOfLeafNeOrCollision` (`i = 0`, any default);
2. walk versus walk, same siblings: leaves `1` and `0` walked one step from index 0 over
   siblings `0` reach the same value.  Properties: `WalkPureInjOrCollision`,
   `PathForgeryChangesWalkOrCollision`, and the walk half of
   `LeafOnlySubstitutionChangesRootOrCollision` (`leaves = [7]`, `idx = 0`, height 1);
3. walk versus walk, siblings changed at one level: leaf `0` walked one step from index 0 over
   `oneAtZero` and over `fun _ => 0`, which agree off level 0 and differ at it.  Properties:
   `WalkVsWalkOrCollision`, `SingleSiblingSubstitutionOrCollision` (`m = 0`);
4. level versus level: `[1]` and `[0]` have the same parent level.  Properties:
   `LevelUpInjOrCollision`, `LevelsInjOrCollision` (`l = 1`, where `levels … 1` is `levelUp`);
5. walk versus a tree node: on the tree `[0]`, the claimed leaf `1` over siblings `0` reaches
   the level-1 node above index 0 (`NoForgedWalkOrCollision`; the original's range premise
   `0 < [0].length` holds too);
6. walk versus the tree root: the same walk is accepted against the root of `[0]` at height 1
   from index `0 < 2^1`; index 0 is occupied by `0`, not by the claimed leaf `1`.
   Properties: `WalkAcceptPinsLeafFreeSibsOrCollision`, `AcceptPinsEntryCasesOrCollision`;
7. update walk with the honest siblings: on `[7]`, the tree's sibling of index 0 at level 0 is
   the padding `0`; over it, leaf `1` (the accepted one) and leaf `0` reach the same root.
   Property: `WalkAcceptPinsLeafOrCollision` (`x = 1`, `y = 0`, `root` the walk of `1`);
8. append walk with the honest frontier siblings: on `[5]`, the tree's sibling of the frontier
   index 1 at level 0 is `5`; over it, leaf `0` reaches the root of `[5] ++ [1]`.
   Property: `NoAppendForgeryWalkOrCollision` (`x = 1`, `y = 0`).

Lists of different lengths: `RootCommitsListCollisionFires` (the collision case of
`RootCommitsListOrBreak`, and `RootCommitsListUnderPadSeparation`) and `PaddingHitFires` (the
padding-hit case of `RootCommitsListOrBreak`). -/
def Properties.PinnedFormsFire : Prop :=
  -- 1. tree versus tree
  (rootOf constHash 0 [1] 1 = rootOf constHash 0 [0] 1
    ∧ ([1] : List UInt256) ≠ [0] ∧ TreeCollision constHash 0 [1] [0] 1 0)
  -- 2. walk versus walk, same siblings
  ∧ (walkPure constHash (fun _ => 0) 0 1 0 1 = walkPure constHash (fun _ => 0) 0 1 0 0
    ∧ (1 : UInt256) ≠ 0 ∧ WalkCollision constHash (fun _ => 0) (fun _ => 0) 0 1 0 1 0)
  -- 3. walk versus walk, siblings changed at level 0 only
  ∧ ((∀ l, l ≠ 0 → oneAtZero l = (fun _ => (0 : UInt256)) l)
    ∧ walkPure constHash oneAtZero 0 1 0 0 = walkPure constHash (fun _ => 0) 0 1 0 0
    ∧ oneAtZero 0 ≠ 0 ∧ WalkCollision constHash oneAtZero (fun _ => 0) 0 1 0 0 0)
  -- 4. level versus level
  ∧ (levelUp constHash 0 [1] = levelUp constHash 0 [0] ∧ LevelCollision constHash 0 [1] [0])
  -- 5. walk versus a tree node
  ∧ ((levels constHash 0 [0] 0).getD 0 (zeros constHash 0 0) ≠ 1
    ∧ walkPure constHash (fun _ => 0) 0 1 0 1
        = (levels constHash 0 [0] (0 + 1)).getD (0 / 2 ^ 1) (zeros constHash 0 (0 + 1))
    ∧ PathCollision constHash 0 [0] (fun _ => 0) 0 1 0 1)
  -- 6. walk versus the tree root
  ∧ (walkPure constHash (fun _ => 0) 0 1 0 1 = rootOf constHash 0 [0] 1
    ∧ ([0] : List UInt256).getD 0 0 ≠ 1
    ∧ ¬ ((0 < ([0] : List UInt256).length ∧ ([0] : List UInt256).getD 0 0 = 1)
        ∨ (([0] : List UInt256).length ≤ 0 ∧ (1 : UInt256) = 0))
    ∧ PathCollision constHash 0 [0] (fun _ => 0) 0 1 0 1)
  -- 7. update walk with the honest siblings
  ∧ ((∀ l, l < 1 → (fun _ => (0 : UInt256)) l
        = (levels constHash 0 [7] l).getD (sibIdx (0 / 2 ^ l)) (zeros constHash 0 l))
    ∧ walkPure constHash (fun _ => 0) 0 1 0 0 = walkPure constHash (fun _ => 0) 0 1 0 1
    ∧ (0 : UInt256) ≠ 1 ∧ WalkCollision constHash (fun _ => 0) (fun _ => 0) 0 1 0 0 1)
  -- 8. append walk with the honest frontier siblings
  ∧ ((∀ l, l < 1 → (fun _ => (5 : UInt256)) l
        = (levels constHash 0 [5] l).getD (sibIdx (([5] : List UInt256).length / 2 ^ l))
            (zeros constHash 0 l))
    ∧ walkPure constHash (fun _ => 5) 0 1 ([5] : List UInt256).length 0
        = rootOf constHash 0 ([5] ++ [1]) 1
    ∧ (0 : UInt256) ≠ 1
    ∧ WalkCollision constHash (fun _ => 5) (fun _ => 5) 0 1 ([5] : List UInt256).length 0 1)

/-- **THE PADDING AMBIGUITY IS LOCATED AS A PADDING HIT, FOR EVERY HASH.**  `[a]` and
`[a, z0]` are within capacity at height 1, have the same root and differ (the instance
`TreeShape.padding_ambiguity_forges_root` is proved with; that statement does not pin it, its
pinned form is `TreeShapeStrong.padding_ambiguity_forges_root_pinned`).
`RootCommitsListOrBreak` locates this as a `PaddingHit` (the second list holds `z0` as a real
leaf at index 1), and no collision is located on any path: no strength of hash prevents it. -/
def Properties.PaddingHitFires : Prop :=
  ∀ (h : Hash) (z0 a : UInt256),
    ([a] : List UInt256).length ≤ 2 ^ 1 ∧ ([a, z0] : List UInt256).length ≤ 2 ^ 1
      ∧ rootOf h z0 [a] 1 = rootOf h z0 [a, z0] 1 ∧ ([a] : List UInt256) ≠ [a, z0]
      ∧ PaddingHit z0 [a] [a, z0] ∧ ∀ i, ¬ TreeCollision h z0 [a] [a, z0] 1 i

/-- **THE COLLISION CASE OF `RootCommitsListOrBreak`, ALONE, AT DIFFERENT LENGTHS.**  Under
`constHash`, `[1]` and `[2, 5]` are within capacity at height 1, neither holds the padding `0`,
and they have the same root.  They differ, there is no padding hit (the second list's entry at
index 1 is `5`, not `0`), they differ at index 0, and the collision is located on index 0's
path.  So this is an instance of the premises of `RootCommitsListOrBreak` and of
`RootCommitsListUnderPadSeparation` on which the original conclusion `L₁ = L₂` fails and the
collision is what holds.  With `PaddingHitFires` (padding hit alone) and
`RootCommitsListOrBreakSatisfiable` (equal lists, neither break), each disjunct of
`RootCommitsListOrBreak` is reached on its own. -/
def Properties.RootCommitsListCollisionFires : Prop :=
  ([1] : List UInt256).length ≤ 2 ^ 1 ∧ ([2, 5] : List UInt256).length ≤ 2 ^ 1
    ∧ (0 : UInt256) ∉ ([1] : List UInt256) ∧ (0 : UInt256) ∉ ([2, 5] : List UInt256)
    ∧ rootOf constHash 0 [1] 1 = rootOf constHash 0 [2, 5] 1
    ∧ ([1] : List UInt256) ≠ [2, 5] ∧ ¬ PaddingHit 0 [1] [2, 5]
    ∧ ([1] : List UInt256).getD 0 0 ≠ ([2, 5] : List UInt256).getD 0 0
    ∧ TreeCollision constHash 0 [1] [2, 5] 1 0

/-! ## Non-vacuity: each property's premises, met with its collision false

Each witness meets every premise of the property it names on an instance (chosen in the
proof) and shows that property's located collision (and, for `RootCommitsListOrBreak`, the
padding hit) is false there.  By the property, the rest of its conclusion then holds on that
instance, which decides what the instance can look like:

* Where the rest is equality of the two sides (`L₁ = L₂`, `x = y`, `s₁ m = s₂ m`), the
  witness necessarily compares an instance with itself: `LevelUpInj`, `LevelsInj`,
  `RootOfInj`, `RootOfAppendInj`, `RootOfSetInj`, `WalkPureInj`, `RootCommitsListOrBreak`,
  `RootCommitsListUnderPadSeparation`, `WalkAcceptPinsLeaf` (`y = x`),
  `SingleSiblingSubstitution`, `NoAppendForgeryWalk`.  Where the rest is "the accepted walk
  opened the tree's own entry", the witness is necessarily an honest proof (an accepted walk
  with no `PathCollision` used the tree's leaf and siblings, `WalkPinsOrCollision`):
  `WalkAcceptPinsLeafFreeSibs`, and `AcceptPinsEntryCases` (at a padded index).  For each of
  these, `PinnedFormsFire`, `RootCommitsListCollisionFires` or `PaddingHitFires` meets the
  same premises with the two sides different, and there the collision (or padding hit) holds.
* Where the rest is weaker than equality of the two sides, the witness has the two sides
  differ and still no collision: `RootPinsEntry`, `WalkVsWalk`, `MemOfRootOfEq`,
  `GetDOfRootOfEq`, `RootOfNeOfNotMem`, `RootNeOfLeafNe`, `PathForgery`, `LeafOnlySubstitution`.
* `NoForgedWalk` has no rest: its premises force the collision, and its witness shows they can
  be met. -/

/-- `RootPinsEntryOrCollision`: met by two DIFFERENT trees with the same root, at an index where
no collision is located (the instance of `RootPinsEntryPinnedToPath`). -/
def Properties.RootPinsEntryOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height i : ℕ),
    i < 2 ^ height ∧ rootOf h z0 L₁ height = rootOf h z0 L₂ height
      ∧ L₁ ≠ L₂ ∧ ¬ TreeCollision h z0 L₁ L₂ height i

/-- `WalkVsWalkOrCollision`: met by two walks over DIFFERENT sibling streams that agree on the
climbed level, with no located collision. -/
def Properties.WalkVsWalkOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (s₁ s₂ : ℕ → UInt256) (k lvl j : ℕ) (x y : UInt256),
    walkPure h s₁ lvl k j x = walkPure h s₂ lvl k j y ∧ s₁ ≠ s₂
      ∧ ¬ WalkCollision h s₁ s₂ lvl k j x y

/-- `LevelUpInjOrCollision`: met by a nonempty level compared with itself. -/
def Properties.LevelUpInjOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z : UInt256) (L₁ L₂ : List UInt256),
    L₁ ≠ [] ∧ L₁.length = L₂.length ∧ levelUp h z L₁ = levelUp h z L₂
      ∧ ¬ LevelCollision h z L₁ L₂

/-- `LevelsInjOrCollision`: met at level 1 by a nonempty list compared with itself. -/
def Properties.LevelsInjOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (l : ℕ),
    L₁ ≠ [] ∧ 0 < l ∧ L₁.length = L₂.length ∧ levels h z0 L₁ l = levels h z0 L₂ l
      ∧ ¬ ∃ l' < l, LevelCollision h (zeros h z0 l') (levels h z0 L₁ l') (levels h z0 L₂ l')

/-- `RootOfInjOrCollision`: met by a nonempty tree within capacity compared with itself. -/
def Properties.RootOfInjOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    L₁ ≠ [] ∧ L₁.length = L₂.length ∧ L₁.length ≤ 2 ^ height
      ∧ rootOf h z0 L₁ height = rootOf h z0 L₂ height
      ∧ ¬ ∃ i < L₁.length, L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i

/-- `RootOfAppendInjOrCollision`: met by appending the same leaf. -/
def Properties.RootOfAppendInjOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (x y : UInt256) (height : ℕ),
    (leaves ++ [x]).length ≤ 2 ^ height
      ∧ rootOf h z0 (leaves ++ [x]) height = rootOf h z0 (leaves ++ [y]) height
      ∧ ¬ TreeCollision h z0 (leaves ++ [x]) (leaves ++ [y]) height leaves.length

/-- `RootOfSetInjOrCollision`: met by writing the same leaf. -/
def Properties.RootOfSetInjOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (idx : ℕ) (x y : UInt256) (height : ℕ),
    idx < leaves.length ∧ leaves.length ≤ 2 ^ height
      ∧ rootOf h z0 (leaves.set idx x) height = rootOf h z0 (leaves.set idx y) height
      ∧ ¬ TreeCollision h z0 (leaves.set idx x) (leaves.set idx y) height idx

/-- `WalkPureInjOrCollision`: met by walking the same leaf. -/
def Properties.WalkPureInjOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (sibs : ℕ → UInt256) (k lvl idx : ℕ) (x y : UInt256),
    0 < k ∧ walkPure h sibs lvl k idx x = walkPure h sibs lvl k idx y
      ∧ ¬ WalkCollision h sibs sibs lvl k idx x y

/-- `RootCommitsListOrBreak`: met by a nonempty tree within capacity compared with itself. -/
def Properties.RootCommitsListOrBreakSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    L₁ ≠ [] ∧ L₁.length ≤ 2 ^ height ∧ L₂.length ≤ 2 ^ height
      ∧ rootOf h z0 L₁ height = rootOf h z0 L₂ height ∧ ¬ PaddingHit z0 L₁ L₂
      ∧ ¬ ∃ i < max L₁.length L₂.length,
          L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i

/-- `RootCommitsListUnderPadSeparation`: met by a nonempty tree, not containing the padding
constant, compared with itself. -/
def Properties.RootCommitsListUnderPadSeparationSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    L₁ ≠ [] ∧ z0 ∉ L₁ ∧ z0 ∉ L₂ ∧ L₁.length ≤ 2 ^ height ∧ L₂.length ≤ 2 ^ height
      ∧ rootOf h z0 L₁ height = rootOf h z0 L₂ height
      ∧ ¬ ∃ i < max L₁.length L₂.length,
          L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i

/-- `NoForgedWalkOrCollision`: its premises (a wrong leaf whose walk reaches the node) can only
be met when a collision is located, by design; they are met under `constHash`
(`PinnedFormsFire`, case 5).  `HonestWalkNoCollision` shows `PathCollision` is no tautology. -/
def Properties.NoForgedWalkOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (k lvl j : ℕ) (x : UInt256)
    (sibs : ℕ → UInt256),
    (levels h z0 L lvl).getD j (zeros h z0 lvl) ≠ x
      ∧ walkPure h sibs lvl k j x
          = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k))

/-- `WalkAcceptPinsLeafFreeSibsOrCollision`: met by the honest proof of an occupied leaf of a
two-leaf tree, which locates no collision. -/
def Properties.WalkAcceptPinsLeafFreeSibsOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ)
    (x : UInt256),
    0 < height ∧ j < L.length ∧ j < 2 ^ height ∧ walkPure h sibs 0 height j x = rootOf h z0 L height
      ∧ ¬ PathCollision h z0 L sibs 0 height j x

/-- `MemOfRootOfEqOrCollision`: met by two DIFFERENT equal-length trees within capacity with
the same root, for a leaf of the first whose first position carries no located collision (the
instance of `RootPinsEntryPinnedToPath`, with `x = 5` at position 2). -/
def Properties.MemOfRootOfEqOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ) (x : UInt256),
    L₁.length = L₂.length ∧ L₁.length ≤ 2 ^ height
      ∧ rootOf h z0 L₁ height = rootOf h z0 L₂ height ∧ x ∈ L₁ ∧ L₁ ≠ L₂
      ∧ ¬ TreeCollision h z0 L₁ L₂ height (L₁.idxOf x)

/-- `GetDOfRootOfEqOrCollision`: met by two DIFFERENT equal-length trees within capacity with
the same root, at an index where no collision is located. -/
def Properties.GetDOfRootOfEqOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height i : ℕ),
    L₁.length = L₂.length ∧ L₁.length ≤ 2 ^ height
      ∧ rootOf h z0 L₁ height = rootOf h z0 L₂ height ∧ L₁ ≠ L₂ ∧ i < L₁.length
      ∧ ¬ TreeCollision h z0 L₁ L₂ height i

/-- `RootOfNeOfNotMemOrCollision`: met by `[1]` versus `[0]` under the colliding `sumHash`,
whose roots differ, with no collision located. -/
def Properties.RootOfNeOfNotMemOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ) (x : UInt256),
    0 < height ∧ L₁.length = L₂.length ∧ L₁.length ≤ 2 ^ height ∧ x ∈ L₁ ∧ x ∉ L₂
      ∧ ¬ TreeCollision h z0 L₁ L₂ height (L₁.idxOf x)

/-- `RootNeOfLeafNeOrCollision`: met by `[1]` versus `[0]` under `sumHash`, no collision. -/
def Properties.RootNeOfLeafNeOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height i : ℕ) (d : UInt256),
    0 < height ∧ L₁.length = L₂.length ∧ L₁.length ≤ 2 ^ height ∧ L₁.getD i d ≠ L₂.getD i d
      ∧ ¬ TreeCollision h z0 L₁ L₂ height i

/-- `PathForgeryChangesWalkOrCollision`: met by leaves `1` and `0` over siblings `0` under
`sumHash`, no collision. -/
def Properties.PathForgeryChangesWalkOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (sibs : ℕ → UInt256) (k lvl idx : ℕ) (x y : UInt256),
    0 < k ∧ x ≠ y ∧ ¬ WalkCollision h sibs sibs lvl k idx x y

/-- `WalkAcceptPinsLeafOrCollision`: met by the honest update walk, for which the only accepted
leaf in its own conclusion, `y = x`, locates no collision. -/
def Properties.WalkAcceptPinsLeafOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256) (leaves : List UInt256) (idx : ℕ)
    (x : UInt256) (height : ℕ) (root : UInt256),
    0 < height ∧ idx < leaves.length ∧ leaves.length ≤ 2 ^ height
      ∧ (∀ l, l < height →
          sibs l = (levels h z0 leaves l).getD (sibIdx (idx / 2 ^ l)) (zeros h z0 l))
      ∧ walkPure h sibs 0 height idx x = root
      ∧ ¬ WalkCollision h sibs sibs 0 height idx x x

/-- `LeafOnlySubstitutionChangesRootOrCollision`: met by overwriting `[7]`'s leaf with `1` or
`0` under `sumHash`; neither collision is located. -/
def Properties.LeafOnlySubstitutionChangesRootOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256) (leaves : List UInt256) (idx : ℕ)
    (x y : UInt256) (height : ℕ),
    0 < height ∧ idx < leaves.length ∧ leaves.length ≤ 2 ^ height ∧ x ≠ y
      ∧ ¬ WalkCollision h sibs sibs 0 height idx x y
      ∧ ¬ TreeCollision h z0 (leaves.set idx x) (leaves.set idx y) height idx

/-- `SingleSiblingSubstitutionOrCollision`: met by the same stream on both sides. -/
def Properties.SingleSiblingSubstitutionOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (s₁ s₂ : ℕ → UInt256) (k lvl m idx : ℕ) (x : UInt256),
    lvl ≤ m ∧ m < lvl + k ∧ (∀ l, l ≠ m → s₁ l = s₂ l)
      ∧ walkPure h s₁ lvl k idx x = walkPure h s₂ lvl k idx x
      ∧ ¬ WalkCollision h s₁ s₂ lvl k idx x x

/-- `NoAppendForgeryWalkOrCollision`: met by the honest frontier walk of the appended leaf. -/
def Properties.NoAppendForgeryWalkOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256) (leaves : List UInt256) (x y : UInt256)
    (height : ℕ),
    0 < height ∧ leaves ≠ [] ∧ leaves.length < 2 ^ height
      ∧ (∀ l, l < height →
          sibs l = (levels h z0 leaves l).getD (sibIdx (leaves.length / 2 ^ l)) (zeros h z0 l))
      ∧ walkPure h sibs 0 height leaves.length y = rootOf h z0 (leaves ++ [x]) height
      ∧ ¬ WalkCollision h sibs sibs 0 height leaves.length y x

/-- `AcceptPinsEntryCasesOrCollision`: met by the honest proof of a PADDED index (the second
case of its conclusion), which locates no collision. -/
def Properties.AcceptPinsEntryCasesOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256),
    L ≠ [] ∧ L.length ≤ j ∧ j < 2 ^ k ∧ walkPure h sibs 0 k j x = rootOf h z0 L k
      ∧ ¬ PathCollision h z0 L sibs 0 k j x

end MerkleSpec.Pinned
