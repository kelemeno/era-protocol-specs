import EraSpec.Contracts.IndexedMerkleTree.Specs.ModelStrong

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

/-!
# Properties: the forged padding witness, pinned to the padding leaf

Statements about `EraSpec.Contracts.IndexedMerkleTree.Specs.ModelStrong`; proofs in
`EraSpec.Contracts.IndexedMerkleTree.Proofs.ModelStrong`.  Pure order theory.

* `forged_padding_witness_pinned` — `forged_padding_witness_breaks_exclusivity` as its docstring
  describes it: for every nonzero `a`, the sound tree `{⟨0, a⟩, ⟨a, 0⟩}` holds `a`, the padding
  leaf `⟨0, 0⟩` is not a member, its window straddles `a`, and no member's window does.
* `padding_leaf_forges_every_delivered` — the same in EVERY `GapSound` tree, for EVERY delivered
  nonzero value.
* `padding_leaf_forges_on_guarded_history` — the same on every state of every guarded history from
  the genesis singleton: real contract histories, with no soundness premise left.
* `gapSound_iff_no_member_straddles_present` — `GapSound` is exactly the statement that no member
  straddles a present key, so membership is the only thing standing between the invariant and the
  forged witness.
* `genesisInsertHistory_guarded` — a guarded history from genesis that delivers a value, meeting
  the premises of the history statement (and of `ResetAndZeroStrong`'s).

So the membership premise `W ∈ s` of `present_not_reclaimable` is not just droppable on one tree:
without it, the reclaim condition is met by the same forged leaf against every delivered leg.
-/

namespace IMTAbstract.ModelStrong

open Clear

/-- **`forged_padding_witness_breaks_exclusivity`, PINNED.**  For every nonzero `a`: the tree
`{⟨0, a⟩, ⟨a, 0⟩}` (the genesis singleton after delivering `a`) is fully sound and holds `a`; the
padding leaf `⟨0, 0⟩` (the abstract leaf of `hashLeaf({0,0,0})`, which pads every empty slot) is
not a member, and its window straddles `a` (key `0 < a`, `nextKey = 0`); and no member's window
straddles `a` (`present_not_reclaimable`).  The tree, the value and the forged leaf are all fixed
by `a`.  It is the instance `s = {⟨0, a⟩, ⟨a, 0⟩}`, `v = a` of
`padding_leaf_forges_every_delivered`, and meets that property's premises. -/
abbrev Properties.forged_padding_witness_pinned {a : UInt256} (ha : a ≠ 0) :=
  SoundState ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf)
    ∧ a ∈ keys ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf)
    ∧ (⟨0, 0⟩ : AbsLeaf) ∉ ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf)
    ∧ (⟨0, 0⟩ : AbsLeaf).key < a
    ∧ ((⟨0, 0⟩ : AbsLeaf).nextKey = 0 ∨ a < (⟨0, 0⟩ : AbsLeaf).nextKey)
    ∧ ¬ ∃ W ∈ ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf), W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey)

/-- **THE PADDING LEAF FORGES A RECLAIM WITNESS FOR EVERY DELIVERED VALUE.**  In any `GapSound`
leaf set `s`, for any nonzero key `v` of `s`: the padding leaf `⟨0, 0⟩` is NOT a member of `s` (a
member with key `0` below the key `v` must have a nonzero `nextKey`), its window straddles `v`,
and no member's window straddles `v`.  So dropping `W ∈ s` from `present_not_reclaimable` breaks
it at every sound tree and every delivered nonzero value, always with the same forged leaf. -/
abbrev Properties.padding_leaf_forges_every_delivered {s : Finset AbsLeaf} {v : UInt256}
    (hgs : GapSound s) (hv : v ∈ keys s) (hv0 : v ≠ 0) :=
  (⟨0, 0⟩ : AbsLeaf) ∉ s
    ∧ (⟨0, 0⟩ : AbsLeaf).key < v
    ∧ ((⟨0, 0⟩ : AbsLeaf).nextKey = 0 ∨ v < (⟨0, 0⟩ : AbsLeaf).nextKey)
    ∧ ¬ ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **ON EVERY REAL HISTORY.**  Along any `GuardedEvolution` from the genesis singleton
`{⟨0, 0⟩}`, at every step `n` and for every delivered nonzero value `v` of `S n`: the padding leaf
is not a leaf of `S n`, it straddles `v`, and no leaf of `S n` does.  Only the guard shape and
genesis are assumed. -/
abbrev Properties.padding_leaf_forges_on_guarded_history {S : ℕ → Finset AbsLeaf}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    {n : ℕ} {v : UInt256} (hv : v ∈ keys (S n)) (hv0 : v ≠ 0) :=
  (⟨0, 0⟩ : AbsLeaf) ∉ S n
    ∧ (⟨0, 0⟩ : AbsLeaf).key < v
    ∧ ((⟨0, 0⟩ : AbsLeaf).nextKey = 0 ∨ v < (⟨0, 0⟩ : AbsLeaf).nextKey)
    ∧ ¬ ∃ W ∈ S n, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **`GapSound` IS EXACTLY "NO MEMBER STRADDLES A PRESENT KEY".**  A leaf set is `GapSound` iff
no member's window straddles any key of the set.  So the invariant the exclusivity theorems carry
is precisely the absence of a reclaim witness, among members, for any delivered value; what it
cannot exclude is a NON-member witness (`padding_leaf_forges_every_delivered`). -/
abbrev Properties.gapSound_iff_no_member_straddles_present (s : Finset AbsLeaf) :=
  GapSound s ↔ ∀ v ∈ keys s, ¬ ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **A GUARDED HISTORY FROM GENESIS THAT DELIVERS A VALUE.**  For nonzero `a`,
`genesisInsertHistory a` is a `GuardedEvolution` and an `Evolution`, starts at the genesis
singleton, holds the two-leaf tree `{⟨0, a⟩, ⟨a, 0⟩}` from step 1 on, and has `a` as a key there.
It meets the premises of `padding_leaf_forges_on_guarded_history` at `n = 1`, `v = a`. -/
abbrev Properties.genesisInsertHistory_guarded {a : UInt256} (ha : a ≠ 0) :=
  GuardedEvolution (genesisInsertHistory a) ∧ Evolution (genesisInsertHistory a)
    ∧ genesisInsertHistory a 0 = ({⟨0, 0⟩} : Finset AbsLeaf)
    ∧ genesisInsertHistory a 1 = ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf)
    ∧ a ∈ keys (genesisInsertHistory a 1)

end IMTAbstract.ModelStrong
