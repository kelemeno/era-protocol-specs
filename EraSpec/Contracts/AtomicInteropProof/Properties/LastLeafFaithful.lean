import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeafFaithful

/-!
# Properties: the last-leaf check with the path length and index the prover's

Statements over `../Specs/LastLeafFaithful.lean`.  Proofs:
`../Proofs/LastLeafFaithful.lean`.

* `AcceptedLastLeafAnyLengthOrBreak` — the replacement for
  `LastLeaf.AcceptedLastLeafOrPinnedBreak` over every submission the deployed verifier
  accepts: any length `k`, any index `j < 2^k`.  The leaf is the last one at the right
  height (and the claimed leaf hash IS that entry), or a `LastLeafAnyLengthBreak`.  No
  hash premise.
* `WrongLengthLastLeafAccepted` and `PaddedIndexLastLeafAccepted` — the two cases the
  old premises (`height` shared, `j < L.length`) excluded are live: each has an
  accepted, zero-checked submission at a non-last position on which the OLD conclusion
  (`j + 1 = L.length ∨ PinnedBreak ∨ PathCollision` on the submitted path) is false,
  and the new disjunct (`HeightBreak`, resp. the padded entry) is the only break.
* `AnyLengthConclusionNotAlways` — the new conclusion is not a tautology.
* `AcceptedLastLeafPinnedLengthOrBreak` / `AcceptedLastLeafAnyLengthOn` — the old
  disjunction, and the bounded collapse to "last leaf", are recovered under exactly two
  extra premises: `k = height` (a length pin the deployed contract does NOT perform for
  `batchLeafProofLen`) and `x ≠ z0` (the claimed leaf hash is not the empty-entry
  constant).  `j < L.length` is no longer assumed.  `AcceptedLastLeafAnyLengthOnSatisfiable`
  exhibits all the bounded premises, under a colliding hash.
-/

namespace MerkleSpec.LastLeafFaithful

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf

/-- **AN ACCEPTED BATCH-LEAF PATH, ANY LENGTH, ANY INDEX: THE LAST LEAF, OR A LOCATED
BREAK.**  If the submitted path passes the deployed checks (`j < 2^k`, it recomputes
chain `c`'s root, the zero check over its `k` levels), then it has the tree's height,
`j` is the last occupied leaf and `x` is that leaf's entry — or a
`LastLeafAnyLengthBreak` is exhibited. -/
def Properties.AcceptedLastLeafAnyLengthOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height → LastBatchPathAccepted h z0 L height sibs k j x →
      (k = height ∧ j + 1 = L.length ∧ L.getD j z0 = x)
        ∨ LastLeafAnyLengthBreak h z0 L sibs k height j x

/-- **A WRONG LENGTH PASSES EVERY DEPLOYED CHECK, AND THE OLD CONCLUSION FAILS.**  Leaves
`[5, 7, 9]` at height 2 under `demoHash`: the EMPTY batch-leaf path at index 0,
presenting the chain root itself as the leaf, is in bounds, recomputes the root, and
passes the (vacuous) zero check.  Index 0 is not the last leaf, there is no
`PinnedBreak` at 0 and no `PathCollision` on the submitted path; the break is the
`HeightBreak`. -/
def Properties.WrongLengthLastLeafAccepted : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height ∧ LastBatchPathAccepted h z0 L height sibs k j x ∧ k ≠ height
      ∧ ¬ (j + 1 = L.length ∨ PinnedBreak h z0 L j ∨ PathCollision h z0 L sibs 0 k j x)
      ∧ HeightBreak h z0 L sibs k height j x

/-- **A PADDED INDEX PASSES EVERY DEPLOYED CHECK, AND THE OLD CONCLUSION FAILS.**  One
leaf `[5]` at height 2 under `demoHash`: the honest path for the EMPTY slot 2,
presenting the empty-entry constant as the leaf, is in bounds, recomputes the root and
passes the zero check (which fires at level 0).  It has the right length, index 2 is
beyond the leaves and not last, there is no `PinnedBreak` and no `PathCollision`, and no
`HeightBreak`; the only break is the padded entry `x = z0`. -/
def Properties.PaddedIndexLastLeafAccepted : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height ∧ LastBatchPathAccepted h z0 L height sibs k j x
      ∧ (∃ l < k, (j / 2 ^ l) % 2 = 0)
      ∧ k = height ∧ L.length ≤ j ∧ x = z0
      ∧ ¬ (j + 1 = L.length ∨ PinnedBreak h z0 L j ∨ PathCollision h z0 L sibs 0 k j x)
      ∧ ¬ HeightBreak h z0 L sibs k height j x

/-- **THE NEW CONCLUSION IS NOT A TAUTOLOGY.**  The honest path for the non-last leaf 1
of `[5, 7, 9]` under the colliding `demoHash` is in bounds and recomputes the root, and
neither the last-leaf outcome nor any `LastLeafAnyLengthBreak` holds.  (The zero check
is the only acceptance condition it fails.) -/
def Properties.AnyLengthConclusionNotAlways : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height ∧ j < 2 ^ k ∧ walkPure h sibs 0 k j x = rootOf h z0 L height
      ∧ ¬ ((k = height ∧ j + 1 = L.length ∧ L.getD j z0 = x)
          ∨ LastLeafAnyLengthBreak h z0 L sibs k height j x)

/-- **THE OLD DISJUNCTION, RECOVERED UNDER TWO NAMED PREMISES.**  With the length pinned
to the tree's height (`k = height`, which the deployed contract does not check for
`batchLeafProofLen`) and a claimed leaf hash that is not the empty-entry constant
(`x ≠ z0`), an accepted path is the last leaf, or a `PinnedBreak`, or a `PathCollision`
on the submitted path.  `j < L.length` is not assumed. -/
def Properties.AcceptedLastLeafPinnedLengthOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height → LastBatchPathAccepted h z0 L height sibs k j x →
    k = height → x ≠ z0 →
      j + 1 = L.length ∨ PinnedBreak h z0 L j ∨ PathCollision h z0 L sibs 0 k j x

/-- **THE BOUNDED COLLAPSE, WITHOUT `j < L.length`.**  Under the two premises above,
domain separation for this tree's entries, and no collision among the tree's own pairs,
the zero cascade's, the tree's pairs along `j`'s path and the pairs this verification
hashed (a finite set fixed by the instance), the accepted leaf IS the last one. -/
def Properties.AcceptedLastLeafAnyLengthOn : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height → LastBatchPathAccepted h z0 L height sibs k j x →
    k = height → x ≠ z0 → EntriesNotEmpty z0 L →
    PairInjOn h (fun p => TreePair h z0 L height p ∨ PathTreePair h z0 L height j p
      ∨ VerifiedPair h sibs height j x p) →
      j + 1 = L.length

/-- **THE BOUNDED PREMISES ARE SATISFIABLE.**  Two leaves `[5, 7]` under the colliding
`demoHash`, height 2, the honest path for leaf 1: every premise of
`AcceptedLastLeafAnyLengthOn` holds, and the zero check fires (and passes) at level 1. -/
def Properties.AcceptedLastLeafAnyLengthOnSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height ∧ LastBatchPathAccepted h z0 L height sibs k j x
      ∧ k = height ∧ x ≠ z0 ∧ EntriesNotEmpty z0 L
      ∧ PairInjOn h (fun p => TreePair h z0 L height p ∨ PathTreePair h z0 L height j p
          ∨ VerifiedPair h sibs height j x p)
      ∧ (∃ l < k, (j / 2 ^ l) % 2 = 0)
      ∧ (∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ h a b = h c d)

end MerkleSpec.LastLeafFaithful
