import EraSpec.Core.Merkle

/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/RootForgery.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ROOT-FORGERY / FALSE-INCLUSION ATTACK VECTORS — the adversarial reading of
  the pure Merkle layer (`specs/MerkleSpec.lean`).

  Everything here is parameterized over an abstract two-child node hash `h`
  together with the PAIR-INJECTIVITY HYPOTHESIS

      hinj : ∀ a b c d, h a b = h c d → a = c ∧ b = d

  which is the abstract stand-in for keccak collision-resistance.  It is a
  HYPOTHESIS of every theorem below — never an axiom, never a `sorry`.  It is
  discharged downstream where `h` is instantiated from the keccak cache (R6).

  Attack vectors covered:

  (a) FALSE INCLUSION (Merkle path soundness).  An attacker publishes a root
      and then claims a leaf value at some index that differs from the honest
      one.  `no_false_inclusion` — equal-width, non-empty, in-capacity leaf
      lists with the SAME root agree at EVERY index; `root_ne_of_leaf_ne` is
      the contrapositive a verifier uses (differ anywhere ⟹ roots differ).
      Engine: `MerkleSpec.rootOf_inj_of_h_inj` (M-D), repackaged pointwise —
      which is the shape an inclusion-proof verifier actually needs.

  (b) PATH FORGERY.  An attacker presents two DIFFERENT leaf values at the
      same index with the SAME sibling path and reaches the same root.
      `no_path_forgery` / `path_forgery_changes_walk` rule this out for the
      walk itself (`MerkleSpec.walkPure_inj`), and `walk_accept_pins_leaf`
      is the composite: combining `MerkleSpec.walkPure_update_orig` (the walk
      IS the whole-tree recomputation of `leaves.set idx x`) with walk
      injectivity, a verifier that accepts a walk against a published root
      simultaneously (i) learns that the published root is the recomputed root
      of the updated tree and (ii) pins the leaf at `idx` uniquely.

  (c) SIBLING SUBSTITUTION.  `walk_congr_sibs_on_climbed` — the walk reads the
      sibling stream only on the levels it climbs, so tampering OUTSIDE
      `[lvl, lvl+k)` is a no-op (nothing is gained, nothing is broken).
      `leaf_substitution_changes_walk` — changing ONLY the leaf, keeping the
      siblings fixed, always changes the walk result.
      `single_sibling_substitution` — changing EXACTLY ONE sibling level (all
      other levels held fixed) also cannot preserve the walk result.

      *** SCOPE, CORRECTED ***  The limitation below is real but narrower than
      it reads, and `specs/MerkleProofSound.lean` now proves the missing part.
      Against ANOTHER WALK — both sides free — `hinj` alone indeed does not
      forbid a compensating multi-level sibling change. Against a TREE ROOT it
      does: peeling the top combine forces the accumulator AND the sibling to be
      the tree's, level by level, so an accepted walk must have used the honest
      siblings (`walk_pins_leaf_and_sibs`). The claim below should be read as
      being about walk-vs-walk only.

      *** HONEST LIMITATION (walk-vs-walk) ***  We do NOT claim, and it is NOT
      provable from `hinj` alone, that an arbitrary change to the sibling stream
      cannot preserve another WALK's value.  With two or more sibling levels free, an adversary
      could in principle pick a compensating pair of sibling values whose
      combines happen to coincide: pair-injectivity constrains each `h`-node
      individually, but it says nothing that forbids a different (leaf,
      sibling-stream) pair from hashing up to the same value once BOTH the
      accumulator and the siblings are allowed to move.  Ruling that out needs
      genuinely more than `hinj` (e.g. that the walk's sibling reads are
      themselves bound to committed storage — the atlas/storage-binding layer,
      not this pure layer).  Only the leaf-injectivity direction, and the
      one-free-sibling-level direction, are established here.

  (d) APPEND FORGERY.  An attacker appends a different leaf at the frontier
      and claims the honest root.  `no_append_forgery` is the `rootOf` form
      (`MerkleSpec.rootOf_append_inj`); `no_append_forgery_walk` is the form
      about the WALK the contract actually performs, obtained by pushing the
      honest root through `MerkleSpec.rootOf_append` (M-B).

  Auxiliary lemma proved here (not available in `MerkleSpec`):
  `walkPure_add`, the split of a `k₁ + k₂`-step walk into two walks; used only
  by `single_sibling_substitution`.

  No new axioms, no `sorry`.  Pure list/arithmetic reasoning on top of
  `MerkleSpec`; no EVM semantics.
-/

namespace AttackVectors.RootForgery

open Clear
open MerkleSpec

/-! ## (a) False inclusion is impossible

Merkle path soundness in the form a verifier consumes: a published root
determines the leaf at *every* index. -/

/-- **(a) FALSE INCLUSION IS IMPOSSIBLE.**  Two leaf lists of equal length
(non-empty, within the tree capacity `2^height`) that recompute to the SAME
root agree at every index — with any `getD` default.  So an attacker cannot
exhibit an index at which its claimed leaf differs from the honest one while
still matching the published root.

Engine: `rootOf_inj_of_h_inj` (M-D) gives `L₁ = L₂`; this is the pointwise
repackaging an inclusion-proof verifier needs. -/
theorem no_false_inclusion (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height)
    (i : ℕ) (d : UInt256) :
    L₁.getD i d = L₂.getD i d :=
  congrArg (fun L => List.getD L i d)
    (rootOf_inj_of_h_inj' h z0 hinj L₁ L₂ height hlen hcap hroot)

/-- **(a), contrapositive.**  Differing at a single index already forces
different roots: the published root is a sound commitment to every leaf. -/
theorem root_ne_of_leaf_ne (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length)
    (hcap : L₁.length ≤ 2 ^ height)
    (i : ℕ) (d : UInt256) (hdiff : L₁.getD i d ≠ L₂.getD i d) :
    rootOf h z0 L₁ height ≠ rootOf h z0 L₂ height := fun hroot =>
  hdiff (no_false_inclusion h z0 hinj L₁ L₂ height hlen hcap hroot i d)

/-! ## (b) Path forgery is impossible -/

/-- **(b) PATH FORGERY IS IMPOSSIBLE.**  Same node hash, same sibling stream,
same starting level / step count / index: if two candidate leaves walk up to
the same value, they are equal.  Direct `walkPure_inj`, stated as the attack
statement (no capacity or in-range hypotheses are needed — this holds for an
arbitrary sibling stream and arbitrary path parities). -/
theorem no_path_forgery (h : Hash) (sibs : ℕ → UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (k lvl idx : ℕ) (x y : UInt256)
    (hwalk : walkPure h sibs lvl k idx x = walkPure h sibs lvl k idx y) :
    x = y :=
  walkPure_inj h sibs hinj k lvl idx x y hwalk

/-- **(b), contrapositive.**  Two distinct claimed leaves on the same path
produce distinct walk results. -/
theorem path_forgery_changes_walk (h : Hash) (sibs : ℕ → UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (k lvl idx : ℕ) (x y : UInt256) (hxy : x ≠ y) :
    walkPure h sibs lvl k idx x ≠ walkPure h sibs lvl k idx y := fun hwalk =>
  hxy (no_path_forgery h sibs hinj k lvl idx x y hwalk)

/-! ## (b) composite — an accepted walk pins the leaf against the tree -/

/-- **(b) COMPOSITE — a verifier accepting a walk pins the leaf.**  Suppose the
sibling stream is the honest one (read from the PRE-update tree at the sibling
indices, with the `zeros` default beyond the frontier, exactly what the
contract fetches), `idx` is in range and the tree is within capacity.  If a
verifier accepts the walk of `x` from `idx` against a published `root`, then

* the published root is exactly the whole-tree recomputation of
  `leaves.set idx x` (`walkPure_update_orig`, M-A), and
* no other leaf value `y` can be accepted against that same root
  (`walkPure_inj`, M-D).

Together: the accepted walk pins the leaf at `idx` uniquely. -/
theorem walk_accept_pins_leaf (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (leaves : List UInt256) (idx : ℕ) (x : UInt256) (height : ℕ) (root : UInt256)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (idx / 2 ^ l)) (zeros h z0 l))
    (haccept : walkPure h sibs 0 height idx x = root) :
    rootOf h z0 (leaves.set idx x) height = root ∧
      ∀ y : UInt256, walkPure h sibs 0 height idx y = root → y = x := by
  refine ⟨?_, ?_⟩
  · rw [← walkPure_update_orig h z0 sibs leaves idx x height hidx hcap hsibs]
    exact haccept
  · intro y hy
    exact walkPure_inj h sibs hinj height 0 idx y x (by rw [hy, haccept])

/-! ## (c) Sibling substitution

The provable half, plus the explicit statement of what is NOT provable (see the
header): pair-injectivity pins the LEAF against a fixed sibling stream, and
pins a SINGLE free sibling level, but it does not by itself forbid a
compensating multi-level sibling change. -/

/-- **(c) FRAME.**  The walk reads the sibling stream only on the levels
`[lvl, lvl+k)` it climbs; agreeing there makes the walks equal.  Consequence
for the attacker: tampering with sibling values outside the climbed window is
a pure no-op — it neither forges nor invalidates anything.  (Re-export of
`walkPure_congr_sibs` in attack form.) -/
theorem walk_congr_sibs_on_climbed (h : Hash) (s₁ s₂ : ℕ → UInt256)
    (k lvl idx : ℕ) (x : UInt256)
    (hagree : ∀ l, lvl ≤ l → l < lvl + k → s₁ l = s₂ l) :
    walkPure h s₁ lvl k idx x = walkPure h s₂ lvl k idx x :=
  walkPure_congr_sibs h s₁ s₂ k lvl idx x hagree

/-- **(c) LEAF-ONLY SUBSTITUTION.**  An attacker who changes ONLY the leaf,
keeping every sibling, cannot preserve the walk result — and correspondingly
cannot preserve the recomputed root of the updated tree.  Both halves come
from pair-injectivity (`walkPure_inj` / `rootOf_set_inj`); the converse claim
about sibling changes is deliberately NOT made (header). -/
theorem leaf_only_substitution_changes_root (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (sibs : ℕ → UInt256) (leaves : List UInt256) (idx : ℕ) (x y : UInt256)
    (height : ℕ) (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hxy : x ≠ y) :
    walkPure h sibs 0 height idx x ≠ walkPure h sibs 0 height idx y ∧
      rootOf h z0 (leaves.set idx x) height ≠ rootOf h z0 (leaves.set idx y) height :=
  ⟨fun hwalk => hxy (walkPure_inj h sibs hinj height 0 idx x y hwalk),
   fun hroot => hxy (rootOf_set_inj h z0 hinj leaves idx x y height hidx hcap hroot)⟩

/-- Splitting a walk: `k₁ + k₂` steps from `lvl` is `k₁` steps from `lvl`
followed by `k₂` steps from `lvl + k₁` at the halved index.  (Auxiliary; not
in `MerkleSpec`.) -/
theorem walkPure_add (h : Hash) (sibs : ℕ → UInt256) :
    ∀ (k₁ k₂ lvl idx : ℕ) (x : UInt256),
      walkPure h sibs lvl (k₁ + k₂) idx x
        = walkPure h sibs (lvl + k₁) k₂ (idx / 2 ^ k₁) (walkPure h sibs lvl k₁ idx x)
  | 0, k₂, lvl, idx, x => by simp
  | k₁ + 1, k₂, lvl, idx, x => by
      have hidx : idx / 2 / 2 ^ k₁ = idx / 2 ^ (k₁ + 1) := by
        rw [Nat.div_div_eq_div_mul, show 2 * 2 ^ k₁ = (2 : ℕ) ^ (k₁ + 1) from by ring]
      rw [show k₁ + 1 + k₂ = (k₁ + k₂) + 1 from by omega, walkPure_succ, walkPure_succ,
          walkPure_add h sibs k₁ k₂ (lvl + 1) (idx / 2), hidx,
          show lvl + 1 + k₁ = lvl + (k₁ + 1) from by omega]

/-- **(c) SINGLE-SIBLING SUBSTITUTION.**  If two sibling streams agree
everywhere EXCEPT at one climbed level `m`, and the walks of the same leaf
agree, then they agree at `m` too: with a single free sibling level there is no
compensating change.  (This is as far as `hinj` reaches — see the header for
why two or more free sibling levels are out of scope.) -/
theorem single_sibling_substitution (h : Hash) (s₁ s₂ : ℕ → UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (k lvl m idx : ℕ) (x : UInt256)
    (hm1 : lvl ≤ m) (hm2 : m < lvl + k)
    (hagree : ∀ l, l ≠ m → s₁ l = s₂ l)
    (heq : walkPure h s₁ lvl k idx x = walkPure h s₂ lvl k idx x) :
    s₁ m = s₂ m := by
  -- split `k` as (m - lvl) + (k₂ + 1): the prefix below `m`, the step at `m`,
  -- and the suffix above `m`.
  obtain ⟨k₂, hk⟩ : ∃ k₂, k = (m - lvl) + (k₂ + 1) := ⟨k - (m - lvl) - 1, by omega⟩
  have hlvl : lvl + (m - lvl) = m := by omega
  -- the prefix walks agree (all levels below `m` are ≠ m)
  have hpre : walkPure h s₁ lvl (m - lvl) idx x = walkPure h s₂ lvl (m - lvl) idx x :=
    walkPure_congr_sibs h s₁ s₂ (m - lvl) lvl idx x
      (fun l _ hl2 => hagree l (by omega))
  -- split both walks at level `m`, then rewrite the `s₂` suffix walk into an
  -- `s₁` one (the streams agree above `m`)
  rw [hk, walkPure_add h s₁ (m - lvl) (k₂ + 1) lvl idx x,
      walkPure_add h s₂ (m - lvl) (k₂ + 1) lvl idx x, hpre, hlvl,
      walkPure_succ, walkPure_succ,
      walkPure_congr_sibs h s₂ s₁ k₂ (m + 1) (idx / 2 ^ (m - lvl) / 2) _
        (fun l hl1 _ => (hagree l (by omega)).symm)] at heq
  -- the suffix walk is injective in its accumulator
  have hstep := walkPure_inj h s₁ hinj k₂ (m + 1) (idx / 2 ^ (m - lvl) / 2) _ _ heq
  by_cases hpar : idx / 2 ^ (m - lvl) % 2 = 1
  · rw [if_pos hpar, if_pos hpar] at hstep
    exact (hinj _ _ _ _ hstep).1
  · rw [if_neg hpar, if_neg hpar] at hstep
    exact (hinj _ _ _ _ hstep).2

/-! ## (d) Append forgery is impossible -/

/-- **(d) APPEND FORGERY — `rootOf` form.**  Appending different leaves to the
same frontier gives different roots (`rootOf_append_inj`, M-D). -/
theorem no_append_forgery (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (leaves : List UInt256) (x y : UInt256) (height : ℕ)
    (hcap : (leaves ++ [x]).length ≤ 2 ^ height)
    (hroot : rootOf h z0 (leaves ++ [x]) height = rootOf h z0 (leaves ++ [y]) height) :
    x = y :=
  rootOf_append_inj h z0 hinj leaves x y height hcap hroot

/-- **(d) APPEND FORGERY — walk form (what the contract performs).**  The
honest root after appending `x` at the frontier is the frontier walk of `x`
with the OLD-tree sibling stream (`rootOf_append`, M-B).  So an attacker that
runs the SAME walk on a claimed leaf `y` and matches the honest published root
must have `y = x`: the frontier walk pins the appended leaf. -/
theorem no_append_forgery_walk (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (leaves : List UInt256) (x y : UInt256) (height : ℕ)
    (hcap : leaves.length < 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (leaves.length / 2 ^ l))
        (zeros h z0 l))
    (hforge : walkPure h sibs 0 height leaves.length y
      = rootOf h z0 (leaves ++ [x]) height) :
    y = x := by
  rw [rootOf_append h z0 sibs leaves x height hcap hsibs] at hforge
  exact walkPure_inj h sibs hinj height 0 leaves.length y x hforge

end AttackVectors.RootForgery
