import EraSpec.Contracts.FullMerkle.Specs.Model

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/- EXTRACTED from contracts-formal-verification (`specs/specs/MerkleSpec.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  PURE MERKLE SPEC — the EVM-free Merkle layer of the root-fidelity track
  (ROOT_FIDELITY_BLUEPRINT.md §1.1).

  `FullMerkle`-shaped trees: level `l+1` pairs up level `l` left-to-right,
  and a lone left child at the frontier is combined with the level-`l` zero
  (`_zeros[l]` in the contract) as its right sibling.  Everything is
  parameterized over an abstract two-child hash `h` and base zero `z0`;
  `h` is instantiated per-theorem from the keccak cache downstream (R6) —
  the model has no global pure keccak.

  Main results (tags match the blueprint):
  * M-C — frontier arithmetic: `levels_length` (+ ceiling form), `levels_nil`,
    `levels_length_pos`, `levels_length_le`, `div_le_levels_length`,
    `div_pow_eq_zero`.
  * M-A — `walkPure_update` / `walkPure_update_orig`: the one-path sibling
    walk recomputes the WHOLE tree root of `leaves.set idx x`.  The engine
    `walkPure_levels` is the intermediate-accumulator form (each partial
    walk value = the parent-level entry on the updated path); the off-path
    helper is `levels_set_off_path`.
  * M-B — `rootOf_append`: appending a leaf at the frontier equals the walk
    from index `leaves.length` whose sibling stream reads the OLD tree via
    `getD` with default `zeros l` — out-of-frontier right siblings collapse
    to the `_zeros` read automatically, matching `stepEdge` and the
    `pushNewLeaf` walk (blueprint §0.2, last bullet).  List surgery in
    `levels_append`; walk bridge in `walkPure_appendPath`.

  Sibling indices and path indices are kept in `ℕ` (`idx / 2^l`, `sibIdx`);
  bridging to `Fin`/UInt256 `shiftRight` is deliberately left to the
  concrete layer (blueprint §4.7).

  * M-D — `rootOf_inj_of_h_inj`: pointwise injectivity of `rootOf` from
    pair-injectivity of `h` (the tree-shaped generalization of
    `foldRoot_binding`).  Engine `levelUp_inj` (equal-width levels) lifts
    through `levels_inj`; `levels_height_singleton` collapses a non-full
    tree's top level to its root.  Node-hash injectivity is discharged
    downstream from keccak injectivity (R6).

  Pure list/arithmetic reasoning — no EVM semantics, no extra axioms.
-/

namespace MerkleSpec


open Clear


abbrev Properties.zeros_zero (h : Hash) (z0 : UInt256) :=
  zeros h z0 0 = z0


abbrev Properties.zeros_succ (h : Hash) (z0 : UInt256) (l : ℕ) :=
  zeros h z0 (l + 1) = h (zeros h z0 l) (zeros h z0 l)


abbrev Properties.levelUp_nil (h : Hash) (z : UInt256) :=
  levelUp h z [] = []


abbrev Properties.levelUp_single (h : Hash) (z a : UInt256) :=
  levelUp h z [a] = [h a z]


abbrev Properties.levelUp_cons₂ (h : Hash) (z a b : UInt256) (rest : List UInt256) :=
  levelUp h z (a :: b :: rest) = h a b :: levelUp h z rest


abbrev Properties.levelUp_pair (h : Hash) (z a b : UInt256) :=
  levelUp h z [a, b] = [h a b]


abbrev Properties.levels_zero (h : Hash) (z0 : UInt256) (leaves : List UInt256) :=
  levels h z0 leaves 0 = leaves


abbrev Properties.levels_succ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) :=
  levels h z0 leaves (l + 1) = levelUp h (zeros h z0 l) (levels h z0 leaves l)


abbrev Properties.rootOf_def (h : Hash) (z0 : UInt256) (leaves : List UInt256) (height : ℕ) :=
  rootOf h z0 leaves height = (levels h z0 leaves height).headD (zeros h z0 height)


abbrev Properties.sibIdx_ne (j : ℕ) :=
  sibIdx j ≠ j


abbrev Properties.walkPure_zero (h : Hash) (sibs : ℕ → UInt256) (lvl idx : ℕ) (x : UInt256) :=
  walkPure h sibs lvl 0 idx x = x


abbrev Properties.walkPure_succ (h : Hash) (sibs : ℕ → UInt256) (lvl k idx : ℕ) (x : UInt256) :=
  walkPure h sibs lvl (k + 1) idx x
        = walkPure h sibs (lvl + 1) k (idx / 2)
            (if idx % 2 = 1 then h (sibs lvl) x else h x (sibs lvl))


abbrev Properties.appendPath_zero (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (x : UInt256) :=
  appendPath h z0 leaves x 0 = x


abbrev Properties.appendPath_succ (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (x : UInt256) (l : ℕ) :=
  appendPath h z0 leaves x (l + 1)
        = if leaves.length / 2 ^ l % 2 = 1 then
            h ((levels h z0 leaves l).getD (leaves.length / 2 ^ l - 1) (zeros h z0 l))
              (appendPath h z0 leaves x l)
          else
            h (appendPath h z0 leaves x l) (zeros h z0 l)


/-! ## `levelUp` structure -/

/-- One level halves the width, rounding up. -/
abbrev Properties.levelUp_length (h : Hash) (z : UInt256) :=
  ∀ L : List UInt256, (levelUp h z L).length = (L.length + 1) / 2


/-- The parent entry `j` combines the child entries `2j` and `2j+1`; the
`getD` default `z` on the right child is exactly the frontier-edge zero. -/
abbrev Properties.levelUp_getD (h : Hash) (z d : UInt256) :=
  ∀ (L : List UInt256) (j : ℕ), 2 * j < L.length →
        (levelUp h z L).getD j d = h (L.getD (2 * j) d) (L.getD (2 * j + 1) z)


/-- `levelUp` distributes over an append at an even cut. -/
abbrev Properties.levelUp_append_even (h : Hash) (z : UInt256) :=
  ∀ A B : List UInt256, A.length % 2 = 0 →
        levelUp h z (A ++ B) = levelUp h z A ++ levelUp h z B


/-- `levelUp` commutes with an even-length prefix. -/
abbrev Properties.levelUp_take_even (h : Hash) (z : UInt256) :=
  ∀ (q : ℕ) (L : List UInt256), 2 * q ≤ L.length →
        levelUp h z (L.take (2 * q)) = (levelUp h z L).take q


/-! ## M-C — frontier arithmetic -/

/-- The empty tree has empty levels. -/
abbrev Properties.levels_nil (h : Hash) (z0 : UInt256) :=
  ∀ l, levels h z0 [] l = []


/-- **M-C.**  Level `l` of a nonempty tree has width `⌈n / 2^l⌉`, in the
`Nat.div` phrasing that recurses cleanly: `(n - 1) / 2^l + 1`. -/
abbrev Properties.levels_length (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (hne : leaves.length ≠ 0) :=
  ∀ l, (levels h z0 leaves l).length = (leaves.length - 1) / 2 ^ l + 1


/-- M-C, ceiling form: the width is `(n + 2^l - 1) / 2^l`. -/
abbrev Properties.levels_length_ceil (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (hne : leaves.length ≠ 0) (l : ℕ) :=
  (levels h z0 leaves l).length = (leaves.length + 2 ^ l - 1) / 2 ^ l


/-- M-C: every level of a nonempty tree is nonempty. -/
abbrev Properties.levels_length_pos (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (hne : leaves.length ≠ 0) (l : ℕ) :=
  0 < (levels h z0 leaves l).length


/-- M-C, upper bound: the level width never exceeds the floor path index
plus one — the entry `⌊n/2^l⌋ + 1` (and beyond) is always outside, so an
even frontier path always reads the `zeros` default. -/
abbrev Properties.levels_length_le (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) :=
  (levels h z0 leaves l).length ≤ leaves.length / 2 ^ l + 1


/-- M-C, lower bound: the floor path index is inside (or at) the level. -/
abbrev Properties.div_le_levels_length (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) :=
  leaves.length / 2 ^ l ≤ (levels h z0 leaves l).length


/-- `set` preserves every level width. -/
abbrev Properties.levels_set_length (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (idx : ℕ) (x : UInt256) :=
  ∀ l, (levels h z0 (leaves.set idx x) l).length = (levels h z0 leaves l).length


/-- M-C: an in-tree index collapses to 0 at the top (`Nat.div_eq_of_lt`,
re-exported for downstream convenience). -/
abbrev Properties.div_pow_eq_zero {idx k : ℕ} (hidx : idx < 2 ^ k) :=
  idx / 2 ^ k = 0


/-! ## M-A — the update walk recomputes the whole tree -/

/-- **M-A helper.**  Off the updated path, the levels of `leaves.set idx x`
agree with the levels of `leaves`: entry `j ≠ idx / 2^l` of level `l` is
unchanged.  (Sibling reads live here, since `sibIdx j ≠ j`.) -/
abbrev Properties.levels_set_off_path (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (idx : ℕ) (x : UInt256) :=
  ∀ (l j : ℕ) (d : UInt256), j ≠ idx / 2 ^ l →
        (levels h z0 (leaves.set idx x) l).getD j d = (levels h z0 leaves l).getD j d


/-- **M-A engine (intermediate-accumulator form).**  If the walk starts at
absolute level `lvl` on the level-`lvl` entry `j` of the tree over `L`, and
the sibling stream matches the tree (`getD` with default `zeros l` — the
frontier edge reads the zero automatically), then after `k` steps the
accumulator is the level-`lvl+k` entry `j / 2^k`.  Every intermediate
accumulator of the walk is therefore the corresponding on-path node. -/
abbrev Properties.walkPure_levels (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (L : List UInt256) :=
  ∀ k lvl j : ℕ,
        j < (levels h z0 L lvl).length →
        (∀ l, lvl ≤ l → l < lvl + k →
          sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l)) →
        walkPure h sibs lvl k j ((levels h z0 L lvl).getD j (zeros h z0 lvl))
          = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k))


/-- **M-A `walkPure_update`.**  Under the in-tree bounds, if the sibling
stream reads the UPDATED tree's levels at the sibling index (with default
`zeros l` beyond the frontier), the walk from `idx` with accumulator `x`
computes the root of `leaves.set idx x`. -/
abbrev Properties.walkPure_update (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (idx : ℕ) (x : UInt256) (height : ℕ)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 (leaves.set idx x) l).getD (sibIdx (idx / 2 ^ l))
        (zeros h z0 l)) :=
  walkPure h sibs 0 height idx x = rootOf h z0 (leaves.set idx x) height


/-- **M-A, old-tree sibling form** (what the contract walk actually reads:
siblings are FETCHED from pre-update storage).  Follows from
`walkPure_update` via `levels_set_off_path` since `sibIdx j ≠ j`. -/
abbrev Properties.walkPure_update_orig (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (idx : ℕ) (x : UInt256) (height : ℕ)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (idx / 2 ^ l)) (zeros h z0 l)) :=
  walkPure h sibs 0 height idx x = rootOf h z0 (leaves.set idx x) height


/-! ## M-B — appending at the frontier is a walk from `leaves.length` -/

/-- **M-B list surgery.**  Appending one leaf turns every level `l` into the
old level truncated at the path index `n / 2^l` plus the new path node:
the appended path is always the LAST entry of its level, old entries left
of it are untouched, and old entries at/right of it (the odd-path left
sibling absorbed into the new node) disappear into the path node. -/
abbrev Properties.levels_append (h : Hash) (z0 : UInt256) (leaves : List UInt256) (x : UInt256) :=
  ∀ l, levels h z0 (leaves ++ [x]) l
        = (levels h z0 leaves l).take (leaves.length / 2 ^ l)
          ++ [appendPath h z0 leaves x l]


/-- **M-B walk bridge.**  With the sibling stream reading the OLD tree at
`sibIdx (n / 2^l)` (default `zeros l` — every even level at the frontier
reads the zero, since the right sibling is outside the old level), the walk
from level `lvl` reproduces the append-path nodes. -/
abbrev Properties.walkPure_appendPath (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (x : UInt256) :=
  ∀ k lvl : ℕ,
        (∀ l, lvl ≤ l → l < lvl + k →
          sibs l = (levels h z0 leaves l).getD (sibIdx (leaves.length / 2 ^ l))
            (zeros h z0 l)) →
        walkPure h sibs lvl k (leaves.length / 2 ^ lvl) (appendPath h z0 leaves x lvl)
          = appendPath h z0 leaves x (lvl + k)


/-- **M-B `rootOf_append`.**  For a non-full tree, the root after appending
`x` is the update walk from the frontier index `leaves.length` whose sibling
stream reads the OLD tree: at odd path indices the real left neighbor, at
even path indices the `getD` default `zeros l` (the right sibling is beyond
the old frontier) — exactly `stepEdge`'s `_zeros[l]` read at every even
level of the contract's walk #2, where `idx = maxN = count`. -/
abbrev Properties.rootOf_append (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (x : UInt256) (height : ℕ)
    (hcap : leaves.length < 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (leaves.length / 2 ^ l))
        (zeros h z0 l)) :=
  rootOf h z0 (leaves ++ [x]) height = walkPure h sibs 0 height leaves.length x


/-! ## M-D — root injectivity from node-hash injectivity

The tree-shaped generalization of `foldRoot_binding`: when the two-child
hash `h` is injective on the pairs it is fed, the recomputed root pins the
whole leaf multiset — same width and same root ⟹ same leaves.  Node-hash
injectivity `hinj` is discharged downstream from keccak injectivity (R6),
exactly as the abstract `h` is instantiated from the keccak cache. -/

/-- `levelUp` is injective on equal-width levels when `h` is pair-injective:
a lone left tail combines with the fixed zero `z`, so its parent still
determines it. -/
abbrev Properties.levelUp_inj (h : Hash) (z : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) :=
  ∀ L₁ L₂ : List UInt256, L₁.length = L₂.length →
        levelUp h z L₁ = levelUp h z L₂ → L₁ = L₂


/-- Level width depends only on the leaf-list width. -/
abbrev Properties.levels_length_eq (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (hlen : L₁.length = L₂.length) :=
  ∀ l, (levels h z0 L₁ l).length = (levels h z0 L₂ l).length


/-- Equal-width leaf lists whose level-`l` lists coincide are equal. -/
abbrev Properties.levels_inj (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (hlen : L₁.length = L₂.length) :=
  ∀ l, levels h z0 L₁ l = levels h z0 L₂ l → L₁ = L₂


/-- **M-D.**  For a non-full tree (`0 < width ≤ 2^height`), the level-`height`
list is a singleton, so it equals its root. -/
abbrev Properties.levels_height_singleton (h : Hash) (z0 : UInt256) (L : List UInt256)
    (height : ℕ) (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height) :=
  levels h z0 L height = [rootOf h z0 L height]


/-- **M-D — `rootOf_inj_of_h_inj`.**  When the node hash is pair-injective,
the recomputed root of a non-full tree pins the whole leaf list: same width,
same root ⟹ same leaves.  The tree-shaped `foldRoot_binding`. -/
abbrev Properties.rootOf_inj_of_h_inj (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :=
  L₁ = L₂


/-- **M-D binding corollary.**  Appending different leaves to the *same*
frontier of a non-full tree yields different roots: the recomputed root
pins the just-appended leaf.  The tree-level statement behind
`refund is bound to the committed bundle hash`. -/
abbrev Properties.rootOf_append_inj (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (leaves : List UInt256) (x y : UInt256) (height : ℕ)
    (hcap : (leaves ++ [x]).length ≤ 2 ^ height)
    (hroot : rootOf h z0 (leaves ++ [x]) height
      = rootOf h z0 (leaves ++ [y]) height) :=
  x = y


/-- **M-D binding corollary (interior leaves).**  Overwriting one leaf with
a different value changes the recomputed root of a non-full tree: the root
pins *every* leaf, not only the appended one.  Companion to
`rootOf_append_inj`. -/
abbrev Properties.rootOf_set_inj (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (leaves : List UInt256) (idx : ℕ) (x y : UInt256) (height : ℕ)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hroot : rootOf h z0 (leaves.set idx x) height
      = rootOf h z0 (leaves.set idx y) height) :=
  x = y


/-- **M-D walk-level binding.**  The update walk is injective in its leaf
accumulator when `h` is pair-injective: each level combines the accumulator
with a sibling via `h`, so injectivity propagates from the root back down to
the leaf, regardless of the sibling stream or path parities.  The `walkPure`
shadow of `rootOf_set_inj`, and the walk-level form of "the recomputed root
pins the written leaf" (R8). -/
abbrev Properties.walkPure_inj (h : Hash) (sibs : ℕ → UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) :=
  ∀ (k lvl idx : ℕ) (x y : UInt256),
        walkPure h sibs lvl k idx x = walkPure h sibs lvl k idx y → x = y


/-- **WALK SIBLING FRAME.**  `walkPure` reads the sibling stream only at the
levels `[lvl, lvl+k)` it actually climbs, so two streams agreeing there give
equal walks — the frame that lets a caller supply siblings level-by-level and
lets the atlas re-anchor the sibling reads between levels (R2). -/
abbrev Properties.walkPure_congr_sibs (h : Hash) (s₁ s₂ : ℕ → UInt256) :=
  ∀ (k lvl idx : ℕ) (x : UInt256),
        (∀ l, lvl ≤ l → l < lvl + k → s₁ l = s₂ l) →
        walkPure h s₁ lvl k idx x = walkPure h s₂ lvl k idx x


/-- **M-D WITHOUT THE NONEMPTINESS HYPOTHESIS.**  `rootOf_inj_of_h_inj` requires
`L₁.length ≠ 0`, but that hypothesis is SPURIOUS: two equal-length lists that are
empty are equal outright, so the degenerate case needs no Merkle reasoning at all.

Worth removing because `hne` is the one hypothesis of M-D that
`AttackVectors.TreeShape` does NOT exhibit a counterexample for — it proved `hlen`
and `hcap` load-bearing but left `hne` unexamined, and this shows why: it was never
needed. -/
abbrev Properties.rootOf_inj_of_h_inj' (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :=
  L₁ = L₂


end MerkleSpec
