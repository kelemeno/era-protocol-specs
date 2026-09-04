import EraSpec.Core.IMT

/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/ResetAndZero.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ATTACK VECTORS: TREE RESET / RE-INITIALIZATION, and the ZERO-VALUE SENTINEL.

  Two attack surfaces of the `L2InteropCommitmentTree`, settled abstractly
  over `IMTAbstract` (pure order theory, axiom-free, no EVM semantics).

  ## (A) TREE-RESET / RE-INITIALIZATION

  The concrete contract guards `setup`/`initL2` to run AT MOST ONCE (the
  `IMTAlreadyInitialized` revert and the one-time `initL2` guard).  Why it
  must: re-initializing the tree back to the genesis singleton would ERASE
  every delivered leg from the key set, and an erased leg is (by
  `reclaimable_iff_absent`) reclaimable again — deliver, reset, reclaim is a
  double spend.  Formally:

  * `evolution_forbids_forgetting` — the anti-reset theorem, the explicit
    contrapositive of `evolution_keys_mono`: along ANY `Evolution`, a value
    present at step `m` and absent at a later step `n` is a contradiction.
    Keys never shrink; no sequence of legitimate operations forgets a
    delivered leg.

  * `resetHistory_not_evolution` — a RESET IS NOT AN `Evolution`: the
    concrete history that delivers `a` at step 0 and reverts to genesis at
    step 1 (`resetHistory`) fails to be an `Evolution`.  The reset step can
    be neither a no-op (the sets differ on key `a`) nor a guarded insert
    (inserts only ADD keys); `evolution_keys_mono` on the hypothetical
    history yields `a ∈ {0}`, contradicting `a ≠ 0`.  So a reset is not
    merely un-guarded — it is outside the transition relation entirely.

  ## GOVERNANCE CAVEAT

  Re-initialization is precisely a GOVERNANCE-EXCEPTED action: an authorised
  upgrade or migration that swaps the tree state is OUTSIDE the `Evolution`
  model by construction (the model's steps are the contract's own guarded
  operations, nothing else).  These theorems therefore bound what a
  NON-PRIVILEGED attacker can achieve through the contract's public
  interface; they say nothing about — and cannot protect against — a
  privileged governance actor performing an upgrade.  The one-time-init
  guard is exactly the mechanism that keeps reset out of the public
  interface and inside governance.

  ## (B) ZERO-VALUE SENTINEL

  Index 0 of the tree holds the sentinel leaf `⟨0, 0⟩`, so the commit value
  `0` is "pre-delivered" at genesis.  An attacker using `v = 0` gains
  nothing — the zero value is structurally inert:

  * `zero_always_present` — `0` is a key of EVERY snapshot along any
    evolution from a genesis containing it (`genesis_zero_mem` +
    `evolution_keys_mono`).

  * `zero_not_reclaimable_along_evolution` — hence `0` is NEVER
    reclaimable: no leaf of any snapshot carries a window straddling `0`
    (via `present_not_reclaimable`).  No refund can ever be extracted for
    the sentinel value.

  * `zero_never_reclaimable` — independent confirmation, with NO
    hypotheses at all: in ANY leaf set whatsoever (sound or not, evolved or
    not), no leaf satisfies `W.key < 0` — `0` is the minimum of
    `Fin (2^256)`.  The reclaim gate's witness precondition is
    unsatisfiable for `v = 0` on order grounds alone.

  * `guarded_never_inserts_zero` — `0` can never be FRESHLY inserted along
    a `GuardedEvolution` from genesis: the dedup gate `v ∉ keys s` is
    unsatisfiable for `v = 0` (and, independently, so is the low-leaf guard
    `W.key < 0`).  No step of a real contract history ever performs the
    insert operation with value `0`.

  Together: `v = 0` can be neither delivered (B3) nor reclaimed (B2) — the
  sentinel is dead weight to an attacker, which is why
  `reclaim_witness_available` may harmlessly except it (`v ≠ 0`).
-/

namespace AttackVectors.ResetAndZero

open Clear IMTAbstract

/-! ## (A) Tree reset / re-initialization -/

/-- **THE ANTI-RESET THEOREM.**  Along any `Evolution`, a value present at
step `m` cannot be absent at any later step `n`: the key set never shrinks
(contrapositive packaging of `evolution_keys_mono`).  No sequence of
legitimate tree operations — inserts and no-ops — can erase a delivered
leg, so "reset the tree, then reclaim the erased legs" is not reachable
through the contract's own transition relation. -/
theorem evolution_forbids_forgetting
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S)
    {v : UInt256} {m n : ℕ} (hmn : m ≤ n)
    (hmem : v ∈ keys (S m)) (habs : v ∉ keys (S n)) : False :=
  habs (evolution_keys_mono hevo hmn hmem)

/-- The reset history: genesis at step 0, one insert of `a` at the 0 → 1
boundary, then a RESET back to the genesis singleton at the 1 → 2 boundary
(and genesis forever after).  This is exactly what a re-invocation of
`setup`/`initL2` would produce after a delivery. -/
def resetHistory (a : UInt256) : ℕ → Finset AbsLeaf :=
  fun n => if n = 1 then imtInsert {⟨0, 0⟩} ⟨0, 0⟩ a else {⟨0, 0⟩}

/-- Step 1 of the reset history HAS delivered `a`. -/
theorem resetHistory_delivers (a : UInt256) :
    a ∈ keys (resetHistory a 1) := by
  have h1 : resetHistory a 1 = imtInsert ({⟨0, 0⟩} : Finset AbsLeaf) ⟨0, 0⟩ a := rfl
  rw [h1]
  exact imtInsert_key_mem (Finset.mem_singleton_self _)

/-- Step 2 of the reset history has FORGOTTEN `a`: after the reset the key
set is back to `{0}`. -/
theorem resetHistory_forgets {a : UInt256} (ha : a ≠ 0) :
    a ∉ keys (resetHistory a 2) := by
  have h2 : resetHistory a 2 = ({⟨0, 0⟩} : Finset AbsLeaf) := rfl
  rw [h2]
  intro hmem
  obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hL
  rw [hL] at hLkey
  exact ha hLkey.symm

/-- **A RESET HISTORY IS NOT AN `Evolution`.**  The history that delivers a
nonzero `a` and then reverts to genesis violates the transition relation:
were it an `Evolution`, `evolution_keys_mono` across the reset boundary
(1 ≤ 2) would carry `a` from the post-delivery key set into the genesis key
set `{0}` — contradicting `a ≠ 0`.  Re-initialization is not a mis-guarded
tree operation; it is no tree operation at all.  (It is exactly the
governance-excepted action the one-time-init guard removes from the public
interface — see the header.) -/
theorem resetHistory_not_evolution {a : UInt256} (ha : a ≠ 0) :
    ¬ Evolution (resetHistory a) := by
  intro hevo
  exact evolution_forbids_forgetting hevo (Nat.le_succ 1)
    (resetHistory_delivers a) (resetHistory_forgets ha)

/-! ## (B) Zero-value sentinel -/

/-- **THE SENTINEL IS ALWAYS PRESENT.**  Along any evolution whose genesis
contains the zero key (as the genesis singleton `{⟨0,0⟩}` does —
`genesis_zero_mem`), `0` is a key of EVERY snapshot. -/
theorem zero_always_present
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S)
    (hzero : (0 : UInt256) ∈ keys (S 0)) (n : ℕ) :
    (0 : UInt256) ∈ keys (S n) :=
  evolution_keys_mono hevo (Nat.zero_le n) hzero

/-- **THE SENTINEL IS NEVER RECLAIMABLE (invariant route).**  Along any
evolution from a sound base containing the zero key, NO snapshot carries a
leaf whose window straddles `0`: the sentinel is permanently present
(`zero_always_present`), and presence kills every straddling window
(`present_not_reclaimable`).  An attacker can never extract a refund for
the zero commit value. -/
theorem zero_not_reclaimable_along_evolution
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S) (h0 : SoundState (S 0))
    (hzero : (0 : UInt256) ∈ keys (S 0)) (n : ℕ) :
    ¬ ∃ W ∈ S n, W.key < (0 : UInt256)
        ∧ (W.nextKey = 0 ∨ (0 : UInt256) < W.nextKey) :=
  present_not_reclaimable (evolution_sound hevo h0 n).1
    (zero_always_present hevo hzero n)

/-- **THE SENTINEL IS NEVER RECLAIMABLE (order route).**  Independent
confirmation needing NO hypotheses whatsoever: in ANY leaf set — sound or
not, reachable or not — no leaf satisfies the reclaim witness precondition
for `v = 0`, because nothing is strictly below `0` in `Fin (2^256)`.  The
zero value is un-reclaimable on order grounds alone. -/
theorem zero_never_reclaimable (s : Finset AbsLeaf) :
    ¬ ∃ W ∈ s, W.key < (0 : UInt256)
        ∧ (W.nextKey = 0 ∨ (0 : UInt256) < W.nextKey) := by
  rintro ⟨W, _, hlt, _⟩
  exact absurd hlt (by simp)

/-- **ZERO IS NEVER FRESHLY INSERTED.**  Along any `GuardedEvolution` from
the genesis singleton, no step performs the guarded insert with value `0`:
the dedup gate `v ∉ keys (S n)` is unsatisfiable for `v = 0`, since the
sentinel key is present at every snapshot (`zero_always_present` through
`guardedEvolution_isEvolution`).  (Independently, the low-leaf guard
`W.key < 0` is already unsatisfiable — `zero_never_reclaimable`'s order
argument — so the guard fails twice over.)  The zero value can be neither
delivered nor reclaimed: structurally inert. -/
theorem guarded_never_inserts_zero
    {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S)
    (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf)) (n : ℕ) :
    ¬ ∃ W : AbsLeaf, W ∈ S n ∧ W.key < (0 : UInt256)
        ∧ (W.nextKey = 0 ∨ (0 : UInt256) ≤ W.nextKey)
        ∧ (0 : UInt256) ∉ keys (S n)
        ∧ S (n+1) = imtInsert (S n) W 0 := by
  rintro ⟨W, _, _, _, hnot, _⟩
  have h0s : SoundState (S 0) := by rw [hgen]; exact genesis_soundState
  have hzero : (0 : UInt256) ∈ keys (S 0) := by
    rw [hgen]; exact genesis_zero_mem
  exact hnot (zero_always_present (guardedEvolution_isEvolution hge h0s) hzero n)

end AttackVectors.ResetAndZero
