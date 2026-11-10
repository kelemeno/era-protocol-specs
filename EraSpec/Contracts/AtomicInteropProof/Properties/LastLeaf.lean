import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeaf

/-!
# Properties: the last-leaf check identifies the last leaf, or breaks the hash

`_verifyLastBatchInRoot` requires every left-child sibling on the proven leaf's
path to be the empty-subtree hash.  `LastLeafOrBreak` does not assume hash
injectivity: the conclusion is "the leaf is last, **or** a `HashBreak` is
exhibited".  `NotHashBreak` and `AcceptedLastLeafOrBreak` (the version for a submitted
path) take global pair-injectivity, which no `UInt256` hash meets
(`Contracts.InteropCommitmentTree.not_nodeInj`), so they are vacuous as stated.
Proofs: `../Proofs/LastLeaf.lean`.
-/

namespace MerkleSpec.LastLeaf

open Clear MerkleSpec MerkleSpec.Verifier

/-- Assuming both idealizations — node pair injectivity and no occupied entry equal
to the empty-entry constant — a `HashBreak` is impossible. -/
def Properties.NotHashBreak : Prop :=
  ∀ {h : Hash} {z0 : UInt256} {L : List UInt256},
    (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) → EntriesNotEmpty z0 L →
    ¬ HashBreak h z0 L

/-- **THE CHECK IDENTIFIES THE LAST LEAF, OR BREAKS THE HASH.**  Over the tree's own
siblings, with no injectivity: if every left-child sibling on `j`'s path is the
empty-subtree hash, then `j` is the last occupied leaf, or a break is exhibited. -/
def Properties.LastLeafOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ),
    L.length ≤ 2 ^ height → j < L.length →
    (∀ l < height, sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l)) →
    (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) →
    j + 1 = L.length ∨ HashBreak h z0 L

/-- **AND THE SAME FOR AN AUTHENTICATED PATH.**  When the submitted path recomputes the
tree's own root, its siblings are the tree's (`MerkleSpec.Verifier.walk_pins`; this
step uses pair injectivity), so the check's conclusion holds for the proof as
submitted. -/
def Properties.AcceptedLastLeafOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256),
      L.length ≤ 2 ^ height → j < L.length →
      walkPure h sibs 0 height j x = rootOf h z0 L height →
      (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) →
      j + 1 = L.length ∨ HashBreak h z0 L


/-- **`HashBreak` IS ALWAYS INHABITED.**  Added during the collision-form repair.
`nodeCollision` accepts any four words, and every `UInt256` hash has a collision, so
"last leaf, or a `HashBreak`" is true of every tree and every hash: the
disjunctions above carry no information as stated.  `Properties.LastLeafOrPinnedBreak`
(below) pins the break to a node of the tree. -/
def Properties.HashBreakAlways : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256), HashBreak h z0 L

/-! ## Pinned forms (no hash premise, or a bounded one)

The statements above are empty: `HashBreak` always holds, and the accepted-path
version assumes global pair-injectivity.  The ones below replace the break with
`PinnedBreak` (a collision on the subtree that starts at `j + 1`) and the
injectivity with `MerkleSpec.Verifier.PathCollision` (a collision at a named level
of the submitted path), or bound the no-collision premise to the finite set of
pairs the instance hashes.  Each comes with an anti-vacuity witness. -/

/-- **THE CHECK IDENTIFIES THE LAST LEAF, OR A PINNED BREAK.**  `LastLeafOrBreak`
with the always-true `HashBreak` replaced by `PinnedBreak h z0 L j`.  Over the
tree's own siblings, no hash premise. -/
def Properties.LastLeafOrPinnedBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ),
    L.length ≤ 2 ^ height → j < L.length →
    (∀ l < height, sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l)) →
    (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) →
    j + 1 = L.length ∨ PinnedBreak h z0 L j

/-- **THE PINNED BREAK IS NOT A TAUTOLOGY.**  There is a hash with collisions, a
tree, and a NON-last leaf `j` at which no `PinnedBreak` exists.  So
`j + 1 = L.length ∨ PinnedBreak h z0 L j` is false there: the disjunction says
something, and what makes it true in `LastLeafOrPinnedBreak` is the zero check. -/
def Properties.PinnedBreakNotAlways : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (j : ℕ),
    (∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ h a b = h c d)
      ∧ j + 1 < L.length ∧ ¬ PinnedBreak h z0 L j

/-- The break is about the leaf after `j`: when `j` is last (or beyond), there is
none, for every hash. -/
def Properties.NoPinnedBreakAtEnd : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (j : ℕ),
    L.length ≤ j + 1 → ¬ PinnedBreak h z0 L j

/-- **AN ACCEPTED SUBMITTED PATH: LAST LEAF, A PINNED BREAK, OR A PATH COLLISION.**
`AcceptedLastLeafOrBreak` without its global-injectivity premise: the step pinning
the submitted siblings to the tree's is `MerkleSpec.Verifier.walk_pins_or_collision`,
whose failure is a `PathCollision` at a named level of this path. -/
def Properties.AcceptedLastLeafOrPinnedBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ)
    (x : UInt256),
      L.length ≤ 2 ^ height → j < L.length →
      walkPure h sibs 0 height j x = rootOf h z0 L height →
      (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) →
      j + 1 = L.length ∨ PinnedBreak h z0 L j ∨ PathCollision h z0 L sibs 0 height j x

/-- **ITS PREMISES ARE SATISFIABLE, WITH THE CHECK EXERCISED.**  Two leaves under
`demoHash`, height 2, the honest path for leaf 1: the walk is accepted, and the
zero check fires (and passes) at level 1. -/
def Properties.AcceptedLastLeafOrPinnedBreakSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ)
    (x : UInt256),
      L.length ≤ 2 ^ height ∧ j < L.length
      ∧ walkPure h sibs 0 height j x = rootOf h z0 L height
      ∧ (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l)
      ∧ (∃ l < height, (j / 2 ^ l) % 2 = 0)

/-- **ITS CONCLUSION IS NOT A TAUTOLOGY.**  An accepted path (honest, so
`walkPure … = rootOf …`) at a non-last leaf, under a colliding hash, where neither a
`PinnedBreak` nor a `PathCollision` exists.  The zero check is the only premise of
`AcceptedLastLeafOrPinnedBreak` this instance fails. -/
def Properties.AcceptedPinnedConclusionNotAlways : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ)
    (x : UInt256),
      L.length ≤ 2 ^ height ∧ j < L.length
      ∧ walkPure h sibs 0 height j x = rootOf h z0 L height
      ∧ ¬ (j + 1 = L.length ∨ PinnedBreak h z0 L j ∨ PathCollision h z0 L sibs 0 height j x)

/-- **NO PINNED BREAK UNDER A BOUNDED NO-COLLISION PREMISE.**  The replacement for
`NotHashBreak`: injectivity only on the tree's own pairs and the zero cascade
(`TreePair`, a finite instance-determined set), and domain separation only for this
tree's entries. -/
def Properties.NoPinnedBreakOn : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ),
    L.length ≤ 2 ^ height → EntriesNotEmpty z0 L →
    PairInjOn h (TreePair h z0 L height) → ¬ PinnedBreak h z0 L j

/-- **AN ACCEPTED PATH WITH THE CHECK IS THE LAST LEAF, UNDER A BOUNDED PREMISE.**
The collapse of `AcceptedLastLeafOrPinnedBreak`: if `h` has no collision among the
tree's pairs, the zero cascade's, and the `height` pairs this verification hashed,
and no entry of this tree is the empty constant, then the leaf is last. -/
def Properties.AcceptedLastLeafOn : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ)
    (x : UInt256),
      L.length ≤ 2 ^ height → j < L.length → EntriesNotEmpty z0 L →
      PairInjOn h (fun p => TreePair h z0 L height p ∨ VerifiedPair h sibs height j x p) →
      walkPure h sibs 0 height j x = rootOf h z0 L height →
      (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) →
      j + 1 = L.length

/-- **THE BOUNDED PREMISES ARE SATISFIABLE.**  One instance meets every premise of
`AcceptedLastLeafOn` (hence of `NoPinnedBreakOn`, whose pair set is smaller), with
the zero check exercised, under the colliding `demoHash`. -/
def Properties.AcceptedLastLeafOnSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ)
    (x : UInt256),
      L.length ≤ 2 ^ height ∧ j < L.length ∧ EntriesNotEmpty z0 L
      ∧ PairInjOn h (TreePair h z0 L height)
      ∧ PairInjOn h (fun p => TreePair h z0 L height p ∨ VerifiedPair h sibs height j x p)
      ∧ walkPure h sibs 0 height j x = rootOf h z0 L height
      ∧ (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l)
      ∧ (∃ l < height, (j / 2 ^ l) % 2 = 0)
      ∧ (∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ h a b = h c d)

end MerkleSpec.LastLeaf
