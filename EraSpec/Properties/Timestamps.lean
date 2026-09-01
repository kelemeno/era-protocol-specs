import EraSpec.Core.IMT

/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/Timestamps.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ATTACK VECTOR: TIMESTAMP / SETTLEMENT-ORDERING MANIPULATION.

  Every exclusivity theorem of `IMTAbstract` that mentions a deadline
  (`delivered_and_reclaimed_impossible`, `timed_out_leg_reclaimable_not_deliverable`,
  `delivered_leg_available_forever`, `guardedEvolution_delivered_available_forever`)
  carries the hypothesis `htmono : Monotone t`, where `t : ℕ → UInt256` maps a
  snapshot index to the settlement timestamp reported for that snapshot, and `D`
  is the leg's deadline.  Delivery is gated by `t i ≤ D` ("the snapshot the
  membership proof is verified against settled on time"); reclaim is gated by
  `D < t (j+1)` ("snapshot `j` is pinned as the LAST on-time one").

  The attack: a sequencer — or anyone who can influence which timestamp is
  reported for which settled root — reports settlement times OUT OF ORDER, so
  that a LATER snapshot claims an EARLIER timestamp.  The two gates then read
  the history in incompatible orders: the reclaim gate believes snapshot `j` is
  the last on-time snapshot, while the delivery gate accepts a strictly later
  snapshot as on-time.

  What this file establishes.

  * `monotone_timestamps_indispensable` — THE HEADLINE.  Without `Monotone t`
    the exclusivity genuinely FAILS.  For every nonzero commit value `a` there
    is a concrete history `S` (a `GuardedEvolution`, hence a real contract run
    shape, from the sound genesis `{⟨0,0⟩}`), a concrete NON-monotone `t`, and a
    concrete deadline `D`, admitting SIMULTANEOUSLY
      – on-time delivery evidence for `a`  (`t 2 ≤ D` and `a ∈ keys (S 2)`), and
      – a deadline-pinned reclaim witness for `a` (`D < t 1`, and the genesis
        leaf `⟨0,0⟩ ∈ S 0` straddles `a`).
    Both gates pass for the same value: the leg is delivered AND refunded.  So
    the reported-settlement-time ORDERING is security-critical, not bookkeeping.
    The two gates touch DIFFERENT timestamps (`t 2` for delivery, `t 1` for the
    pin), and non-monotonicity lets `t 2 < t 1` — that inversion is the whole
    attack.

  * `attackTime_not_monotone` — the exhibited `t` is explicitly not monotone
    (`t 1 = a > 0 = t 2` while `1 ≤ 2`), stated separately as well as bundled.

  * `monotone_blocks_the_attack` — the companion: with `Monotone t` restored the
    very same configuration is impossible.  Cited from
    `IMTAbstract.delivered_and_reclaimed_impossible`, not re-proved.

  * `delivered_and_reclaimed_impossible_local` — SHARPENING (part B).
    Monotonicity is needed only ON THE TWO INDICES ACTUALLY COMPARED: the
    exclusivity proof goes through from the far weaker, purely local hypothesis
    `j + 1 ≤ i → t (j+1) ≤ t i`.  `monotone_gives_local` +
    `delivered_and_reclaimed_impossible_of_local` show the global theorem is a
    corollary, and `attack_violates_local_hypothesis` shows the counterexample
    above violates precisely this local condition — so the local condition, not
    global monotonicity, is the exact security-relevant fact about `t`.

  Honest scope.  This is a sharpness/indispensability result about the ABSTRACT
  model's hypothesis, in the same style as `StaleSnapshot.deadline_gate_indispensable`
  (which drops the deadline comparison) and
  `IMTAbstract.forged_padding_witness_breaks_exclusivity` (which drops witness
  membership).  It does NOT claim that the deployed system reports non-monotone
  timestamps; it establishes that IF it ever did, the delivery/reclaim
  exclusivity would break, with an explicit double-spend configuration as
  evidence.  Nothing here says anything about how `t` is produced on chain.

  Pure order theory over `IMTAbstract` — axiom-free, no EVM semantics.
-/

namespace AttackVectors.Timestamps

open IMTAbstract
open Clear

/-! ## The attack history and the inverted timestamp assignment -/

/-- The minimal delivery history: genesis `{⟨0,0⟩}` at snapshot 0, one guarded
insert of `a` at the 0 → 1 boundary, constant from 1 on.  So `a` is a key of
EVERY snapshot `≥ 1` — in particular of snapshot 2, which is what lets the
delivery gate and the reclaim pin land on different timestamps. -/
def attackHistory (a : UInt256) : ℕ → Finset AbsLeaf :=
  fun m => if m = 0 then {⟨0, 0⟩} else imtInsert {⟨0, 0⟩} ⟨0, 0⟩ a

/-- The INVERTED settlement-time assignment: every snapshot reports timestamp
`a`, except snapshot 2 which reports `0`.  Snapshot 2 is strictly later than
snapshot 1 yet claims a strictly earlier settlement time — exactly the ordering
a manipulating sequencer would need. -/
def attackTime (a : UInt256) : ℕ → UInt256 :=
  fun m => if m = 2 then 0 else a

private lemma attackHistory_zero (a : UInt256) :
    attackHistory a 0 = ({⟨0, 0⟩} : Finset AbsLeaf) := rfl

private lemma attackHistory_two (a : UInt256) :
    attackHistory a 2 = imtInsert ({⟨0, 0⟩} : Finset AbsLeaf) ⟨0, 0⟩ a := rfl

private lemma attackTime_one (a : UInt256) : attackTime a 1 = a := by
  simp [attackTime]

private lemma attackTime_two (a : UInt256) : attackTime a 2 = 0 := by
  simp [attackTime]

/-- `a` is not a genesis key (the genesis leaf's key is `0`). -/
private lemma a_not_mem_genesis {a : UInt256} (ha : a ≠ 0) :
    a ∉ keys ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro hmem
  obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hL
  rw [hL] at hLkey
  exact ha hLkey.symm

/-- The attack history is a genuine `Evolution`: one guarded insert of `a`
through the genesis leaf's window, then no-ops. -/
theorem attackHistory_evolution {a : UInt256} (ha : a ≠ 0) :
    Evolution (attackHistory a) := by
  intro n
  cases n with
  | zero =>
    exact Or.inr ⟨⟨0, 0⟩, a, Finset.mem_singleton_self _,
      Fin.pos_of_ne_zero ha, Or.inl rfl, rfl⟩
  | succ k => exact Or.inl rfl

/-- Stronger: the attack history is a `GuardedEvolution` — its single insert
satisfies the CONCRETE contract guard (low leaf in the tree, strictly below `a`,
the weak loop-exit window, and the dedup gate `a ∉ keys`).  So the
counterexample is not an artifact of the abstract `Evolution` relation: it is a
history the real insert path can produce. -/
theorem attackHistory_guardedEvolution {a : UInt256} (ha : a ≠ 0) :
    GuardedEvolution (attackHistory a) := by
  intro n
  cases n with
  | zero =>
    exact Or.inr ⟨⟨0, 0⟩, a, Finset.mem_singleton_self _,
      Fin.pos_of_ne_zero ha, Or.inl rfl, a_not_mem_genesis ha, rfl⟩
  | succ k => exact Or.inl rfl

/-- **THE TIMESTAMP ASSIGNMENT IS NOT MONOTONE.**  `1 ≤ 2` but
`attackTime a 1 = a > 0 = attackTime a 2`: the later snapshot reports the
earlier settlement time. -/
theorem attackTime_not_monotone {a : UInt256} (ha : a ≠ 0) :
    ¬ Monotone (attackTime a) := by
  intro hmono
  have h12 : attackTime a 1 ≤ attackTime a 2 :=
    hmono (by omega : (1 : ℕ) ≤ 2)
  rw [attackTime_one, attackTime_two] at h12
  exact absurd h12 (not_le.mpr (Fin.pos_of_ne_zero ha))

/-! ## (A) Monotonicity is indispensable -/

/-- **WITHOUT MONOTONE TIMESTAMPS, DELIVERY AND RECLAIM COEXIST.**  For every
nonzero commit value `a` there are: a history `S` that is both an `Evolution`
and a `GuardedEvolution` from the sound genesis `{⟨0,0⟩}`, a NON-monotone
settlement-time assignment `t`, a deadline `D`, indices `i`, `j` and a leaf `W`
such that

* the DELIVERY gate passes: `t i ≤ D` and `v ∈ keys (S i)`; and
* the RECLAIM gate passes: `D < t (j+1)` pins `j`, and `W ∈ S j` carries a
  window straddling `v`.

Concretely `S = attackHistory a`, `t = attackTime a`, `D = 0`, `v = a`, `i = 2`,
`j = 0`, `W = ⟨0,0⟩`: `t 2 = 0 ≤ 0 = D` with `a ∈ keys (S 2)`, while
`D = 0 < a = t 1`, and the genesis leaf's `nextKey = 0` window straddles `a`.
The same leg is therefore both delivered and refunded — a genuine double-spend.

The `Monotone t` hypothesis of `delivered_and_reclaimed_impossible` is thus
load-bearing: the reported settlement-time ORDERING is a security-critical
input, not bookkeeping.  (Compare
`StaleSnapshot.deadline_gate_indispensable`, which removes the deadline
comparison entirely; here the deadline comparisons are both performed and both
pass, because they read different timestamps and those timestamps are
inverted.) -/
theorem monotone_timestamps_indispensable {a : UInt256} (ha : a ≠ 0) :
    ∃ (S : ℕ → Finset AbsLeaf) (t : ℕ → UInt256) (D v : UInt256)
      (i j : ℕ) (W : AbsLeaf),
      Evolution S ∧ GuardedEvolution S
        ∧ S 0 = ({⟨0, 0⟩} : Finset AbsLeaf) ∧ SoundState (S 0)
        ∧ ¬ Monotone t
        ∧ (t i ≤ D ∧ v ∈ keys (S i))
        ∧ (D < t (j + 1) ∧ W ∈ S j
            ∧ W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)) := by
  refine ⟨attackHistory a, attackTime a, 0, a, 2, 0, ⟨0, 0⟩,
    attackHistory_evolution ha, attackHistory_guardedEvolution ha,
    attackHistory_zero a, ?_, attackTime_not_monotone ha, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, Or.inl rfl⟩⟩
  · rw [attackHistory_zero]; exact genesis_soundState
  · -- delivery is ON TIME at snapshot 2: t 2 = 0 ≤ 0 = D
    rw [attackTime_two]
  · -- a IS a key of snapshot 2 (the set is constant from snapshot 1 on)
    rw [attackHistory_two]
    exact imtInsert_key_mem (Finset.mem_singleton_self _)
  · -- snapshot 0 is deadline-PINNED: D = 0 < a = t 1
    rw [attackTime_one]
    exact Fin.pos_of_ne_zero ha
  · rw [attackHistory_zero]
    exact Finset.mem_singleton_self _
  · exact Fin.pos_of_ne_zero ha

/-- **MONOTONICITY BLOCKS IT.**  With `Monotone t` restored, the configuration
exhibited by `monotone_timestamps_indispensable` is impossible: no history from
a sound base admits both on-time delivery evidence and a deadline-pinned
reclaim witness for the same value.  Direct packaging of
`IMTAbstract.delivered_and_reclaimed_impossible` (cited, not re-proved) — the
exact statement whose hypothesis the counterexample above removes. -/
theorem monotone_blocks_the_attack
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0)) (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {j : ℕ} {W : AbsLeaf} (hpin : D < t (j + 1)) (hW : W ∈ S j)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :
    False :=
  delivered_and_reclaimed_impossible hevo h0.1 h0.2.1 htmono hti hdel
    hpin hW hlow hwin

/-! ## (B) Only LOCAL monotonicity matters

Inspecting the proof of `delivered_and_reclaimed_impossible`, `htmono` is used
exactly once, and only to rule out `j < i`: from `j < i` it derives
`t (j+1) ≤ t i`, which contradicts `D < t (j+1)` and `t i ≤ D`.  Nothing else
about `t` is needed.  So the hypothesis can be weakened to a single
implication about the two indices actually compared. -/

/-- **EXCLUSIVITY FROM LOCAL MONOTONICITY ONLY.**  The delivered-XOR-reclaimed
core holds under the purely local hypothesis `j + 1 ≤ i → t (j+1) ≤ t i`: the
timestamps of ALL OTHER snapshot pairs may be arbitrary — inverted, random,
adversarial.  The contract therefore only needs settlement times to be ordered
between the pinning snapshot `j+1` and the snapshot a delivery proof is
verified against. -/
theorem delivered_and_reclaimed_impossible_local
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    {i j : ℕ} (hloc : j + 1 ≤ i → t (j + 1) ≤ t i)
    (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {W : AbsLeaf} (hpin : D < t (j + 1)) (hW : W ∈ S j)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :
    False := by
  have hij : i ≤ j := by
    by_contra hgt
    push_neg at hgt
    exact absurd hti
      (not_le.mpr (lt_of_lt_of_le hpin (hloc (Nat.succ_le_of_lt hgt))))
  have hkeys : v ∈ keys (S j) := evolution_keys_mono hevo hij hdel
  obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hkeys
  exact gap_excludes_member (evolution_invariant hevo h0 hinj0 j).1
    hW hL hlow hwin hLkey

/-- Global monotonicity gives the local hypothesis for every index pair. -/
theorem monotone_gives_local {t : ℕ → UInt256} (htmono : Monotone t) (i j : ℕ) :
    j + 1 ≤ i → t (j + 1) ≤ t i :=
  fun h => htmono h

/-- **THE GLOBAL THEOREM IS A COROLLARY OF THE LOCAL ONE.**  Re-derives
`delivered_and_reclaimed_impossible`'s statement from
`delivered_and_reclaimed_impossible_local` via `monotone_gives_local`,
confirming the local hypothesis is a genuine weakening (nothing was lost). -/
theorem delivered_and_reclaimed_impossible_of_local
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {j : ℕ} {W : AbsLeaf} (hpin : D < t (j + 1)) (hW : W ∈ S j)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :
    False :=
  delivered_and_reclaimed_impossible_local hevo h0 hinj0
    (monotone_gives_local htmono i j) hti hdel hpin hW hlow hwin

/-- **THE COUNTEREXAMPLE VIOLATES EXACTLY THE LOCAL CONDITION.**  For the
attack configuration of `monotone_timestamps_indispensable` (`i = 2`, `j = 0`),
the local hypothesis `j + 1 ≤ i → t (j+1) ≤ t i` fails: `1 ≤ 2` holds while
`attackTime a 1 = a > 0 = attackTime a 2`.  Together with
`delivered_and_reclaimed_impossible_local` this identifies the single inequality
about reported settlement times on which delivery/reclaim exclusivity rests. -/
theorem attack_violates_local_hypothesis {a : UInt256} (ha : a ≠ 0) :
    ¬ (0 + 1 ≤ 2 → attackTime a (0 + 1) ≤ attackTime a 2) := by
  intro h
  have h12 : attackTime a 1 ≤ attackTime a 2 := h (by omega)
  rw [attackTime_one, attackTime_two] at h12
  exact absurd h12 (not_le.mpr (Fin.pos_of_ne_zero ha))

end AttackVectors.Timestamps
