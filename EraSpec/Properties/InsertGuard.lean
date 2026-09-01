import EraSpec.Core.IMT

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

/-- The two-leaf tree `{⟨0, a⟩, ⟨a, 0⟩}` — genesis plus one delivered value
`a ≠ 0` — is fully sound.  Shared witness state for both sharpness
counterexamples below. -/
theorem two_leaf_soundState {a : UInt256} (ha : a ≠ 0) :
    SoundState ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf) := by
  have hapos : (0 : UInt256) < a := Fin.pos_of_ne_zero ha
  have hnlt : ¬ (a < (0 : UInt256)) := by
    intro h; exact absurd (lt_trans hapos h) (lt_irrefl _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- GapSound
    intro W hW L hL hlt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW hL
    rcases hW with rfl | rfl <;> rcases hL with rfl | rfl <;> simp_all
  · -- KeyInj
    intro A hA B hB hkey
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> simp_all
  · -- NextClosed
    intro W hW hnz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · exact ⟨⟨a, 0⟩, by simp, rfl⟩
    · exact absurd rfl hnz
  · -- WindowPos
    intro W hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · exact Or.inr hapos
    · exact Or.inl rfl

/-- **ATTACK (a): BELOW-WINDOW INSERT IS UNSOUND — guard (ii) is
indispensable.**  For any nonzero `a` and any nonzero `v ≤ a` there is a fully
`SoundState` tree with a genuine member low leaf `W` such that `¬ (W.key < v)`
— guard (ii) is violated, every other guard input is honest — and
`imtInsert s W v` is NOT `WindowPos` (hence NOT `SoundState`): the retargeted
low leaf `⟨W.key, v⟩` carries a nonzero `nextKey` not strictly above its key.
Choosing `v ≠ 0` closes the `nextKey = 0` escape hatch. -/
theorem below_window_insert_breaks_windowPos
    {a v : UInt256} (ha : a ≠ 0) (hv : v ≠ 0) (hle : v ≤ a) :
    ∃ (s : Finset AbsLeaf) (W : AbsLeaf),
      SoundState s ∧ W ∈ s ∧ ¬ (W.key < v)
        ∧ ¬ WindowPos (imtInsert s W v)
        ∧ ¬ SoundState (imtInsert s W v) := by
  refine ⟨{⟨0, a⟩, ⟨a, 0⟩}, ⟨a, 0⟩, two_leaf_soundState ha, by simp,
    not_lt.mpr hle, ?_⟩
  have hnwp : ¬ WindowPos (imtInsert ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf) ⟨a, 0⟩ v) := by
    intro hwp
    -- the retargeted low leaf ⟨a, v⟩ heads the inserted set
    have hmem : (⟨a, v⟩ : AbsLeaf)
        ∈ imtInsert ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf) ⟨a, 0⟩ v := by
      unfold imtInsert
      exact Finset.mem_insert_self _ _
    rcases hwp ⟨a, v⟩ hmem with h0 | hlt
    · exact hv h0
    · exact absurd hlt (not_lt.mpr hle)
  exact ⟨hnwp, fun hss => hnwp hss.2.2.2⟩

/-- **ATTACK (b): DUPLICATE DELIVERY IS BLOCKED — the strict window alone
already forbids replay.**  In any `GapSound` state, a commit value that is
already a key (`v ∈ keys s` — the leg was delivered) admits NO leaf of the
tree satisfying the strict insert window: whatever low leaf a replaying
attacker presents, either `W.key < v` fails or the window fails.  The insert
path for an already-delivered value is unsatisfiable at the witness level —
before the dedup gate is even consulted.  (Anti-replay corollary of
`present_not_reclaimable`.) -/
theorem duplicate_delivery_blocked
    {s : Finset AbsLeaf} {v : UInt256}
    (hgs : GapSound s) (hdup : v ∈ keys s) :
    ∀ W ∈ s, ¬ (W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)) := by
  rintro W hW ⟨hlow, hwin⟩
  exact present_not_reclaimable hgs hdup ⟨W, hW, hlow, hwin⟩

/-- **THE WEAK WINDOW'S ONLY LEAK IS THE BOUNDARY.**  For a delivered value
(`v ∈ keys s`, `GapSound s`), any member leaf satisfying guard (ii) plus the
WEAK loop-exit window (iii) must sit exactly on the boundary `v = W.nextKey`
— the strict cases are killed by `duplicate_delivery_blocked`.  So the dedup
gate (iv) has exactly one job: reject this boundary case.  Attack (c) below
shows the job is real. -/
theorem weak_window_member_forces_boundary
    {s : Finset AbsLeaf} {W : AbsLeaf} {v : UInt256}
    (hgs : GapSound s) (hW : W ∈ s) (hdup : v ∈ keys s)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v ≤ W.nextKey) :
    v = W.nextKey := by
  rcases hwin with h0 | hle
  · exact absurd ⟨W, hW, hlow, Or.inl h0⟩ (present_not_reclaimable hgs hdup)
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact absurd ⟨W, hW, hlow, Or.inr hlt⟩ (present_not_reclaimable hgs hdup)
    · exact heq

/-- **ATTACK (c): WEAK WINDOW WITHOUT DEDUP IS UNSOUND — guard (iv) is
indispensable.**  For any nonzero `a` there is a fully `SoundState` tree, a
member low leaf `W`, and a value `v` satisfying guard (ii) (`W.key < v`) and
the WEAK loop-exit window (iii) (`v ≤ W.nextKey`, here with `v = W.nextKey`
exactly) — yet `v` is already a key.  Performing the insert anyway produces a
set that is NOT `KeyInj` (hence NOT `SoundState`): the new leaf `⟨a, a⟩` and
the surviving old leaf `⟨a, 0⟩` are distinct but share key `a`.  This is the
precise reason `window_strict_of_not_mem` requires `v ∉ keys s`: without the
dedup gate the weak window admits the key-duplicating boundary insert. -/
theorem weak_window_without_dedup_breaks_keyInj {a : UInt256} (ha : a ≠ 0) :
    ∃ (s : Finset AbsLeaf) (W : AbsLeaf) (v : UInt256),
      SoundState s ∧ W ∈ s
        ∧ W.key < v                          -- guard (ii) holds
        ∧ (W.nextKey = 0 ∨ v ≤ W.nextKey)    -- weak window (iii) holds
        ∧ v ∈ keys s                         -- dedup gate (iv) VIOLATED
        ∧ ¬ KeyInj (imtInsert s W v)
        ∧ ¬ SoundState (imtInsert s W v) := by
  have hapos : (0 : UInt256) < a := Fin.pos_of_ne_zero ha
  refine ⟨{⟨0, a⟩, ⟨a, 0⟩}, ⟨0, a⟩, a, two_leaf_soundState ha, by simp,
    hapos, Or.inr (le_refl a),
    Finset.mem_image.mpr ⟨⟨a, 0⟩, by simp, rfl⟩, ?_⟩
  have hninj : ¬ KeyInj (imtInsert ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf) ⟨0, a⟩ a) := by
    intro hinj
    -- the freshly appended leaf ⟨v, W.nextKey⟩ = ⟨a, a⟩
    have h1 : (⟨a, a⟩ : AbsLeaf)
        ∈ imtInsert ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf) ⟨0, a⟩ a := by
      unfold imtInsert
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    -- the untouched old leaf ⟨a, 0⟩ survives the erase of ⟨0, a⟩
    have h2 : (⟨a, 0⟩ : AbsLeaf)
        ∈ imtInsert ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf) ⟨0, a⟩ a := by
      unfold imtInsert
      refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
      refine Finset.mem_erase.mpr ⟨?_, by simp⟩
      intro h
      exact ha (congrArg AbsLeaf.key h)
    -- two distinct leaves share key a
    have heq := hinj ⟨a, a⟩ h1 ⟨a, 0⟩ h2 rfl
    exact ha (congrArg AbsLeaf.nextKey heq)
  exact ⟨hninj, fun hss => hninj hss.2.1⟩

end AttackVectors.InsertGuard
