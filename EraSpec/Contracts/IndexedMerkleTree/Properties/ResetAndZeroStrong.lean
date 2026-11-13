import EraSpec.Contracts.IndexedMerkleTree.Specs.ResetAndZeroStrong

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

/-!
# Properties: the zero sentinel, with its premises load-bearing

Statements about `EraSpec.Contracts.IndexedMerkleTree.Specs.ResetAndZeroStrong`; proofs in
`EraSpec.Contracts.IndexedMerkleTree.Proofs.ResetAndZeroStrong`.  Pure order theory.

* `guardedEvolution_keys_mono` — along ANY guarded history, keys never shrink (no soundness
  premise; `evolution_keys_mono` needs an `Evolution`, which a guarded history is only from a
  sound base).
* `guarded_dedup_gate_rejects_zero` — `guarded_never_inserts_zero` as its docstring describes it:
  along a guarded history from genesis, `0` is a key of every snapshot, so the abstract dedup
  gate `0 ∉ keys (S n)` never passes.  `…_sharp`: dropping either premise breaks it.
* `zero_not_reclaimable_invariant_route` — `zero_not_reclaimable_along_evolution` as its
  docstring describes it: the sentinel is present at every snapshot, and every present key has
  no straddling window.  `…_sharp`: dropping any one of the three premises breaks it.
* `…_satisfiable` — the premises met by `IMTAbstract.ModelStrong.genesisInsertHistory`, a
  history that delivers a value.
-/

namespace AttackVectors.ResetAndZeroStrong

open Clear IMTAbstract IMTAbstract.ModelStrong

/-- **KEYS NEVER SHRINK ALONG A GUARDED HISTORY.**  Along any `GuardedEvolution` (no soundness
premise, no genesis premise), the key set at step `m` is contained in the key set at every later
step: a guarded step is a no-op or an `imtInsert`, and `imtInsert` keeps every key
(`imtInsert_keys_grow`). -/
abbrev Properties.guardedEvolution_keys_mono {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S) :=
  ∀ {m n : ℕ}, m ≤ n → keys (S m) ⊆ keys (S n)

/-- **THE DEDUP GATE REJECTS ZERO AT EVERY SNAPSHOT OF A REAL HISTORY.**  Along any
`GuardedEvolution` from the genesis singleton `{⟨0, 0⟩}`, the sentinel key `0` is a key of every
snapshot, so the abstract dedup gate `v ∉ keys (S n)` is never satisfied by `v = 0`.  This is the
content `guarded_never_inserts_zero`'s docstring describes; that statement's conclusion holds for
every history because of its conjunct `W.key < 0`.  Both premises are needed
(`guarded_dedup_gate_rejects_zero_sharp`).  Only `0 ∈ keys (S 0)` is used from genesis
(`guardedEvolution_keys_mono`).

This is the ABSTRACT gate.  The contract's own gate `valueToIndex[_value] != 0`
(`IndexedMerkleTree.sol:72-74`) does not reject `0`, since `setup` never registers the sentinel;
the contract rejects `0` with `IMTValueZero` (:69-71) and the low-leaf check (:81-83). -/
abbrev Properties.guarded_dedup_gate_rejects_zero {S : ℕ → Finset AbsLeaf}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf)) (n : ℕ) :=
  (0 : UInt256) ∈ keys (S n)

/-- **BOTH PREMISES OF `guarded_dedup_gate_rejects_zero` ARE NEEDED.**  Without genesis: the empty
history (every step a no-op) is a `GuardedEvolution`, does not start at genesis, and `0` is not a
key, so the gate passes for `0`.  Without the guard: `zeroDroppingHistory` starts at genesis, is not
a `GuardedEvolution`, and loses the key `0` at step 1. -/
abbrev Properties.guarded_dedup_gate_rejects_zero_sharp :=
  (GuardedEvolution (constHistory ∅) ∧ constHistory ∅ 0 ≠ ({⟨0, 0⟩} : Finset AbsLeaf)
      ∧ (0 : UInt256) ∉ keys (constHistory ∅ 0))
    ∧ (zeroDroppingHistory 0 = ({⟨0, 0⟩} : Finset AbsLeaf)
      ∧ ¬ GuardedEvolution zeroDroppingHistory
      ∧ (0 : UInt256) ∉ keys (zeroDroppingHistory 1))

/-- `guarded_dedup_gate_rejects_zero` and `guardedEvolution_keys_mono`: their premises are met by
`genesisInsertHistory a`, a guarded history from genesis that delivers the nonzero value `a`. -/
abbrev Properties.guarded_dedup_gate_rejects_zero_satisfiable {a : UInt256} (ha : a ≠ 0) :=
  GuardedEvolution (genesisInsertHistory a)
    ∧ genesisInsertHistory a 0 = ({⟨0, 0⟩} : Finset AbsLeaf)
    ∧ a ∈ keys (genesisInsertHistory a 1)

/-- **THE SENTINEL IS NEVER RECLAIMABLE, BY THE INVARIANT ROUTE.**  Along any `Evolution` from a
sound base containing the zero key: at every snapshot `n`, the sentinel key `0` is present, and
every present key `v` has no leaf of `S n` whose window straddles it.  Taking `v = 0` gives "no
snapshot carries a window straddling `0`" from presence, which is the route
`zero_not_reclaimable_along_evolution`'s docstring describes; that statement's conclusion holds
for every history because of its conjunct `W.key < 0` (for `v = 0` the order argument
`zero_never_reclaimable` already suffices).  Here each premise is needed
(`zero_not_reclaimable_invariant_route_sharp`): the evolution and the zero key for presence, the
evolution and soundness for the second conjunct, which covers every delivered leg.  The second
conjunct is `GapSound (S n)` stated as a reclaim condition
(`IMTAbstract.ModelStrong.Properties.gapSound_iff_no_member_straddles_present`). -/
abbrev Properties.zero_not_reclaimable_invariant_route {S : ℕ → Finset AbsLeaf}
    (hevo : Evolution S) (h0 : SoundState (S 0)) (hzero : (0 : UInt256) ∈ keys (S 0)) (n : ℕ) :=
  (0 : UInt256) ∈ keys (S n)
    ∧ ∀ v ∈ keys (S n), ¬ ∃ W ∈ S n, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **EACH PREMISE OF `zero_not_reclaimable_invariant_route` IS NEEDED.**  For nonzero `a`:

1. without soundness: the constant history at `{⟨0, 0⟩, ⟨a, 0⟩}` is an `Evolution` holding `0`,
   is not sound, holds `a`, and its leaf `⟨0, 0⟩` straddles `a`;
2. without the zero key: the constant history at `{⟨a, 0⟩}` is an `Evolution` from a sound base
   without `0`;
3. without the evolution: `zeroDroppingHistory` starts at a sound base holding `0`, is not an
   `Evolution`, and loses `0` at step 1. -/
abbrev Properties.zero_not_reclaimable_invariant_route_sharp {a : UInt256} (ha : a ≠ 0) :=
  (Evolution (constHistory ({⟨0, 0⟩, ⟨a, 0⟩} : Finset AbsLeaf))
      ∧ (0 : UInt256) ∈ keys ({⟨0, 0⟩, ⟨a, 0⟩} : Finset AbsLeaf)
      ∧ ¬ SoundState ({⟨0, 0⟩, ⟨a, 0⟩} : Finset AbsLeaf)
      ∧ a ∈ keys ({⟨0, 0⟩, ⟨a, 0⟩} : Finset AbsLeaf)
      ∧ ∃ W ∈ ({⟨0, 0⟩, ⟨a, 0⟩} : Finset AbsLeaf), W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey))
    ∧ (Evolution (constHistory ({⟨a, 0⟩} : Finset AbsLeaf))
      ∧ SoundState ({⟨a, 0⟩} : Finset AbsLeaf)
      ∧ (0 : UInt256) ∉ keys ({⟨a, 0⟩} : Finset AbsLeaf))
    ∧ (SoundState (zeroDroppingHistory 0) ∧ (0 : UInt256) ∈ keys (zeroDroppingHistory 0)
      ∧ ¬ Evolution zeroDroppingHistory ∧ (0 : UInt256) ∉ keys (zeroDroppingHistory 1))

/-- `zero_not_reclaimable_invariant_route`: its premises are met by `genesisInsertHistory a`, an
evolution from the sound genesis singleton (which holds `0`) that delivers the nonzero value `a`,
so the second conjunct covers a delivered leg at step 1. -/
abbrev Properties.zero_not_reclaimable_invariant_route_satisfiable {a : UInt256} (ha : a ≠ 0) :=
  Evolution (genesisInsertHistory a) ∧ SoundState (genesisInsertHistory a 0)
    ∧ (0 : UInt256) ∈ keys (genesisInsertHistory a 0)
    ∧ a ∈ keys (genesisInsertHistory a 1)

end AttackVectors.ResetAndZeroStrong
