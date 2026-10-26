import EraSpec.Core.Word


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


/-- Abstract two-child node hash (instantiated from the keccak cache downstream). -/
abbrev Hash := UInt256 → UInt256 → UInt256


/-! ## Definitions -/

/-- The zero cascade: `zeros l` is the all-empty subtree hash at level `l`
(`_zeros[l]` in `FullMerkle`). -/
def zeros (h : Hash) (z0 : UInt256) : ℕ → UInt256
  | 0 => z0
  | l + 1 => h (zeros h z0 l) (zeros h z0 l)


/-- One level up: combine pairwise; a lone left tail combines with the
level zero `z` as its right sibling (the `FullMerkle` frontier edge). -/
def levelUp (h : Hash) (z : UInt256) : List UInt256 → List UInt256
  | [] => []
  | [a] => [h a z]
  | a :: b :: rest => h a b :: levelUp h z rest


/-- The level lists of the tree over `leaves`: `levels 0 = leaves`,
`levels (l+1) = levelUp` with the level-`l` zero. -/
def levels (h : Hash) (z0 : UInt256) (leaves : List UInt256) : ℕ → List UInt256
  | 0 => leaves
  | l + 1 => levelUp h (zeros h z0 l) (levels h z0 leaves l)


/-- The root at a given height: head of the level-`height` list, or the
all-empty hash when there are no leaves. -/
def rootOf (h : Hash) (z0 : UInt256) (leaves : List UInt256) (height : ℕ) : UInt256 :=
  (levels h z0 leaves height).headD (zeros h z0 height)


/-- The sibling index of `j` inside one level: `j-1` for odd `j`, `j+1` for
even `j` (ℕ form of `j XOR 1`). -/
def sibIdx (j : ℕ) : ℕ := if j % 2 = 1 then j - 1 else j + 1


/-- The pure update walk (`updateWalk`'s shadow): starting at absolute level
`lvl`, walk `k` levels up from index `idx` with accumulator `x`, orienting
each combine by the parity of the current index and reading the sibling from
the stream `sibs` at the absolute level. -/
def walkPure (h : Hash) (sibs : ℕ → UInt256) : ℕ → ℕ → ℕ → UInt256 → UInt256
  | _, 0, _, x => x
  | lvl, k + 1, idx, x =>
      walkPure h sibs (lvl + 1) k (idx / 2)
        (if idx % 2 = 1 then h (sibs lvl) x else h x (sibs lvl))


/-- The path values created by appending `x` at the frontier: `appendPath l`
is the level-`l` node on the new leaf's path (used by M-B).  At each level
the left sibling is the old tree's last entry when the path index is odd,
and the level zero when it is even (the path is at the frontier). -/
def appendPath (h : Hash) (z0 : UInt256) (leaves : List UInt256) (x : UInt256) : ℕ → UInt256
  | 0 => x
  | l + 1 =>
      if leaves.length / 2 ^ l % 2 = 1 then
        h ((levels h z0 leaves l).getD (leaves.length / 2 ^ l - 1) (zeros h z0 l))
          (appendPath h z0 leaves x l)
      else
        h (appendPath h z0 leaves x l) (zeros h z0 l)


end MerkleSpec
