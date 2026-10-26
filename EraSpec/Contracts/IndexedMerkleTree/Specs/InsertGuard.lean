import EraSpec.Contracts.IndexedMerkleTree.Specs.Model


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/InsertGuard.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ATTACK VECTORS: INSERT-GUARD BYPASS — every guard conjunct is load-bearing.

  The concrete `L2InteropCommitmentTree` insert is guarded by four conjuncts:
    (i)   the low leaf is really a tree leaf      (`W ∈ s`),
    (ii)  the value is strictly above the low key (`W.key < v`),
    (iii) the weak loop-exit window               (`W.nextKey = 0 ∨ v ≤ W.nextKey`),
    (iv)  the dedup gate                          (`v ∉ keys s`).
  (`IMTAbstract.guarded_insert_sound_step` shows the four TOGETHER perform a
  sound insert; sharpness of (i) is `forged_padding_witness_breaks_exclusivity`
  in `IMTAbstract`.)  This file settles the remaining three conjuncts.

  Results (axiom-free, pure order theory):

  * ATTACK (a) — BELOW-WINDOW INSERT, guard (ii) is indispensable
    (`below_window_insert_breaks_windowPos`): for ANY nonzero `v ≤ W.key`,
    inserting `v` through the low leaf `W = ⟨a, 0⟩` of the fully sound
    two-leaf tree `{⟨0, a⟩, ⟨a, 0⟩}` produces a set that is NOT `WindowPos`
    (hence NOT `SoundState`): the retargeted low leaf `⟨a, v⟩` has a nonzero
    `nextKey` that is not strictly above its key.  An attacker who could skip
    (ii) would corrupt the linked-list order invariant.

  * ATTACK (b) — DUPLICATE DELIVERY, blocked by the strict window alone
    (`duplicate_delivery_blocked`): in any `GapSound` state, a value already
    delivered (`v ∈ keys s`) admits NO leaf satisfying the STRICT insert
    window `W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)` — a replayed insert
    of the same commit value can never exhibit a valid low leaf.  (Anti-replay
    restatement of `present_not_reclaimable`.)  The companion
    `weak_window_member_forces_boundary` pins the ONLY leak the WEAK window
    (iii) leaves open: for a delivered `v`, a weak-window leaf necessarily has
    `v = W.nextKey` exactly — the boundary case that only the dedup gate (iv)
    can reject.

  * ATTACK (c) — WEAK WINDOW WITHOUT DEDUP, guard (iv) is indispensable
    (`weak_window_without_dedup_breaks_keyInj`): on the same sound two-leaf
    tree, `W = ⟨0, a⟩` and `v = a = W.nextKey` satisfy guards (ii) and (iii)
    — the weak window admits the boundary `v = W.nextKey` — while `v` is
    already a key.  Performing that insert yields two DISTINCT leaves
    (`⟨a, a⟩` and `⟨a, 0⟩`) sharing key `a`: the result is NOT `KeyInj`
    (hence NOT `SoundState`).  This duplicate-key state is precisely what
    the dedup gate exists to prevent, and precisely why
    `IMTAbstract.window_strict_of_not_mem` needs its `v ∉ keys s` hypothesis.
-/

namespace AttackVectors.InsertGuard


open Clear IMTAbstract


end AttackVectors.InsertGuard
