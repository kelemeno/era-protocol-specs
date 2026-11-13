import EraSpec.Contracts.IndexedMerkleTree.Specs.ResetAndZero
import EraSpec.Contracts.IndexedMerkleTree.Specs.ModelStrong

/-!
# Contract spec: the zero sentinel, with its premises load-bearing

## Why this file exists

Two statements of `AttackVectors.ResetAndZero` (`ResetAndZero`) carry the conjunct
`W.key < (0 : UInt256)` inside a negated existential:

* `zero_not_reclaimable_along_evolution` (the "invariant route"): `¬ ∃ W ∈ S n, W.key < 0 ∧ …`;
* `guarded_never_inserts_zero` (the dedup gate):
  `¬ ∃ W, W ∈ S n ∧ W.key < 0 ∧ … ∧ 0 ∉ keys (S n) ∧ …`.

Nothing in `Fin (2^256)` is below `0`, so both conclusions hold for EVERY history `S`, with every
premise (`Evolution`, `GuardedEvolution`, soundness, genesis, `0 ∈ keys`) unused.  Neither checks
what its docstring says: that the sentinel stays present and that presence is what blocks the
gate.  (`zero_never_reclaimable` states the order fact honestly, with no hypotheses.)

`../Properties/ResetAndZeroStrong.lean` states the content the docstrings describe, with
conclusions that fail when a premise is dropped:

* the abstract dedup gate `v ∉ keys (S n)` fails for `v = 0` at every snapshot of a guarded history
  from genesis (key monotonicity along guarded histories needs no soundness premise);
* along an evolution from a sound base holding `0`, the sentinel is present at every snapshot and
  every present key (the sentinel and every delivered leg) has no straddling window.

## What the source does (era-contracts `c67894b9`)

`l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol`:

    // insert:
    if (_value == 0) { revert IMTValueZero(); }                                     // :69-71
    if (self.valueToIndex[_value] != 0) { revert IMTValueAlreadyExists(_value); }   // :72-74
    if (lowLeaf.value >= _value) { revert IMTLowLeafValueTooLarge(…); }             // :81-83
    // verifyNonInclusion:
    if (_value == 0) { revert IMTValueZero(); }                                     // :160-162
    if (_lowLeaf.value >= _value) { revert IMTLowLeafValueTooLarge(…); }            // :163-165

`setup` writes the sentinel leaf `{0, 0, 0}` at index 0 (:47-50) but never writes
`valueToIndex[0]`.  So the contract's own dedup gate (:72-74) does NOT reject `0`:
`valueToIndex[0]` stays `0`.  The abstract gate `v ∉ keys s` agrees with it only for `v ≠ 0`
(`Contracts.InteropCommitmentTree.Properties.dedup_gate_sound` takes `v ≠ 0` for this reason).
The contract rejects `0` with the dedicated checks at :69-71 and :160-162, and again with the
low-leaf checks at :81-83 and :163-165.

## Model boundary

Order theory over `Finset AbsLeaf`, as in `Model`.  The two histories below are countermodels:
they show which premise each conclusion needs.
-/

namespace AttackVectors.ResetAndZeroStrong

open Clear IMTAbstract

/-- The history that stays at one leaf set forever: every step is a no-op. -/
def constHistory (s : Finset AbsLeaf) : ℕ → Finset AbsLeaf := fun _ => s

/-- The history that starts at the genesis singleton and drops to the empty set at step 1, losing
the sentinel.  Not a tree operation (`resetHistory` resets to genesis instead). -/
def zeroDroppingHistory : ℕ → Finset AbsLeaf := fun n => if n = 0 then {⟨0, 0⟩} else ∅

end AttackVectors.ResetAndZeroStrong
