import EraSpec.Contracts.IndexedMerkleTree.Specs.Model


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
    reclaimable: no leaf of any snapshot carries a window straddling `0`.
    Its proof goes via `present_not_reclaimable`, but its STATEMENT holds
    for every history with no premise used: a window straddling `0` needs
    `W.key < 0`, so it is `zero_never_reclaimable` at `S n`.  The invariant
    route as a statement whose premises are all needed is
    `ResetAndZeroStrong.zero_not_reclaimable_invariant_route`.

  * `zero_never_reclaimable` — independent confirmation, with NO
    hypotheses at all: in ANY leaf set whatsoever (sound or not, evolved or
    not), no leaf satisfies `W.key < 0` — `0` is the minimum of
    `Fin (2^256)`.  The reclaim gate's witness precondition is
    unsatisfiable for `v = 0` on order grounds alone.

  * `guarded_never_inserts_zero` — no step of a guarded history performs
    the guarded insert with value `0`.  Its conclusion contains the
    low-leaf guard `W.key < 0`, which nothing satisfies, so it holds for
    every history with no premise used; it does not check the dedup-gate
    claim.  That claim (the abstract gate `v ∉ keys (S n)` fails for
    `v = 0` at every snapshot of a guarded history from genesis) is
    `ResetAndZeroStrong.guarded_dedup_gate_rejects_zero`.  The contract's
    own gate `valueToIndex[_value] != 0` does not reject `0` (the sentinel
    is never registered); the contract rejects `0` by `IMTValueZero`.

  Together: `v = 0` can be neither delivered (B3) nor reclaimed (B2) — the
  sentinel is dead weight to an attacker, which is why
  `reclaim_witness_available` may harmlessly except it (`v ≠ 0`).
-/

namespace AttackVectors.ResetAndZero


open Clear IMTAbstract


/-- The reset history: genesis at step 0, one insert of `a` at the 0 → 1
boundary, then a RESET back to the genesis singleton at the 1 → 2 boundary
(and genesis forever after).  This is exactly what a re-invocation of
`setup`/`initL2` would produce after a delivery. -/
def resetHistory (a : UInt256) : ℕ → Finset AbsLeaf :=
  fun n => if n = 1 then imtInsert {⟨0, 0⟩} ⟨0, 0⟩ a else {⟨0, 0⟩}


end AttackVectors.ResetAndZero
