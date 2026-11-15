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
  old premises (`height` shared, `j < L.length`) excluded pass every check the contract
  performs: each has an accepted submission at a non-last position on which the OLD
  conclusion (`j + 1 = L.length ∨ PinnedBreak ∨ PathCollision` on the submitted path)
  is false, and the new disjunct (`HeightBreak`, resp. the padded entry) is the only
  break.  In the model the claimed leaf hash `x` is free; on chain it is the batch-leaf
  hash of a 128-byte preimage, so each instance needs a cross-length keccak preimage (of a
  node hash, resp. of the empty-entry constant).  "Live" therefore means: not excluded by any check
  the contract performs, only by hash domain separation (Specs, model boundary).  The
  wrong-length witness has `k = 0`, so its zero check ranges over no level; only the
  padded one exercises it.
* `AnyLengthConclusionNotAlways` — the new conclusion is not a tautology.
* `AcceptedLastLeafPinnedLengthOrBreak` / `AcceptedLastLeafAnyLengthOn` — the old
  disjunction, and the bounded collapse to "last leaf" (with `x` that leaf's entry), are
  recovered under two extra premises: `k = height` (a length pin the deployed contract
  does NOT perform for `batchLeafProofLen`) and `x ≠ z0` (the claimed leaf hash is not
  the empty-entry constant).  `j < L.length` is no longer assumed.
  `AcceptedLastLeafNoHeightBreakOn` recovers the bounded collapse with `k = height`
  replaced by "no `HeightBreak` located on the instance", which also yields
  `k = height`.  `AcceptedLastLeafAnyLengthOnSatisfiable` exhibits all the bounded
  premises together.
* Witness shapes.  `PaddedIndexLastLeafAccepted` (one leaf at height 2) and
  `AcceptedLastLeafAnyLengthOnSatisfiable` (two leaves at height 2) use tree shapes a
  deployed chain tree does not have: `DynamicIncrementalMerkle.push` grows the tree only
  when it is full (`DynamicIncrementalMerkle.sol:93-108`), so `n ≥ 1` leaves sit at
  height `⌈log2 n⌉`.  The other witnesses use three leaves at height 2, a deployed shape.
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

/-- **A WRONG LENGTH PASSES EVERY CHECK THE CONTRACT PERFORMS, AND THE OLD CONCLUSION
FAILS.**  Leaves `[5, 7, 9]` at height 2 under `demoHash`: the EMPTY batch-leaf path at
index 0, presenting the chain root itself as the leaf, is in bounds, recomputes the
root, and passes the zero check.  Index 0 is not the last leaf, there is no
`PinnedBreak` at 0 and no `PathCollision` on the submitted path; the break is the
`HeightBreak`.

The path has `k = 0`, so the zero check and the `PathCollision` conjunct range over no
level.  In the model the leaf hash `x` is free; on chain it is the batch-leaf hash of a
128-byte preimage, so this instance needs such a preimage of the chain root, a node hash
(the keccak of 64 bytes).  It is excluded only by hash domain separation, not by a check. -/
def Properties.WrongLengthLastLeafAccepted : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height ∧ LastBatchPathAccepted h z0 L height sibs k j x ∧ k ≠ height
      ∧ ¬ (j + 1 = L.length ∨ PinnedBreak h z0 L j ∨ PathCollision h z0 L sibs 0 k j x)
      ∧ HeightBreak h z0 L sibs k height j x

/-- **A PADDED INDEX PASSES EVERY CHECK THE CONTRACT PERFORMS, AND THE OLD CONCLUSION
FAILS.**  One leaf `[5]` at height 2 under `demoHash`: the honest path for the EMPTY
slot 2, presenting the empty-entry constant as the leaf, is in bounds, recomputes the
root and passes the zero check (which fires at level 0).  It has the right length,
index 2 is beyond the leaves and not last, there is no `PinnedBreak` and no
`PathCollision`, and no `HeightBreak`; the only break is the padded entry `x = z0`.

In the model the leaf hash `x` is free; on chain it is the batch-leaf hash of a 128-byte
preimage, so this instance needs such a preimage of the empty-entry constant (itself the
keccak of 96 zero bytes): excluded only by hash domain separation, not by a check.  One leaf at
height 2 is not a shape a deployed chain tree has (one leaf sits at height 0). -/
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
hashed (a finite set fixed by the instance), the accepted leaf IS the last one, and the
claimed leaf hash `x` is its entry.  The tree's pairs along `j`'s path add nothing to
the set (`PathTreePair`): it is the set `LastLeaf.AcceptedLastLeafOn` uses. -/
def Properties.AcceptedLastLeafAnyLengthOn : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height → LastBatchPathAccepted h z0 L height sibs k j x →
    k = height → x ≠ z0 → EntriesNotEmpty z0 L →
    PairInjOn h (fun p => TreePair h z0 L height p ∨ PathTreePair h z0 L height j p
      ∨ VerifiedPair h sibs height j x p) →
      j + 1 = L.length ∧ L.getD j z0 = x

/-- **THE BOUNDED COLLAPSE AT ANY LENGTH, WITH NO LOCATED `HeightBreak`.**  As
`AcceptedLastLeafAnyLengthOn`, with the length pin `k = height` replaced by "the
instance exhibits no `HeightBreak`" and the pairs this verification hashed taken at the
submitted length `k`: the path has the tree's height, `j` is the last occupied leaf, and
`x` is its entry.  `¬ HeightBreak` is a premise about the hash on this instance, and
it covers same-length 64-byte collisions on the walk as well as the cross-length cases
(Specs, model boundary), so it is not implied by preimage-length separation alone. -/
def Properties.AcceptedLastLeafNoHeightBreakOn : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    L.length ≤ 2 ^ height → LastBatchPathAccepted h z0 L height sibs k j x →
    ¬ HeightBreak h z0 L sibs k height j x → x ≠ z0 → EntriesNotEmpty z0 L →
    PairInjOn h (fun p => TreePair h z0 L height p ∨ VerifiedPair h sibs k j x p) →
      k = height ∧ j + 1 = L.length ∧ L.getD j z0 = x

/-- **THE BOUNDED PREMISES ARE SATISFIABLE.**  Two leaves `[5, 7]` under `demoHash`,
height 2, the honest path for leaf 1: every premise of `AcceptedLastLeafAnyLengthOn`
holds, and the zero check fires (and passes) at level 1.  The last conjunct (`h` has a
collision) holds for every `UInt256` hash (`MerkleSpec.Verifier.exists_pair_collision`),
so it adds nothing beyond satisfiability.  Two leaves at height 2 is not a shape a
deployed chain tree has (two leaves sit at height 1). -/
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
