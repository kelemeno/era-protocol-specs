import EraSpec.Contracts.AtomicInteropProof.Specs.Timestamps

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


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


/-- The attack history is a genuine `Evolution`: one guarded insert of `a`
through the genesis leaf's window, then no-ops. -/
abbrev Properties.attackHistory_evolution {a : UInt256} (ha : a ≠ 0) :=
  Evolution (attackHistory a)


/-- Stronger: the attack history is a `GuardedEvolution` — its single insert
satisfies the CONCRETE contract guard (low leaf in the tree, strictly below `a`,
the weak loop-exit window, and the dedup gate `a ∉ keys`).  So the
counterexample is not an artifact of the abstract `Evolution` relation: it is a
history the real insert path can produce. -/
abbrev Properties.attackHistory_guardedEvolution {a : UInt256} (ha : a ≠ 0) :=
  GuardedEvolution (attackHistory a)


/-- **THE TIMESTAMP ASSIGNMENT IS NOT MONOTONE.**  `1 ≤ 2` but
`attackTime a 1 = a > 0 = attackTime a 2`: the later snapshot reports the
earlier settlement time. -/
abbrev Properties.attackTime_not_monotone {a : UInt256} (ha : a ≠ 0) :=
  ¬ Monotone (attackTime a)


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
abbrev Properties.monotone_timestamps_indispensable {a : UInt256} (ha : a ≠ 0) :=
  ∃ (S : ℕ → Finset AbsLeaf) (t : ℕ → UInt256) (D v : UInt256)
        (i j : ℕ) (W : AbsLeaf),
        Evolution S ∧ GuardedEvolution S
          ∧ S 0 = ({⟨0, 0⟩} : Finset AbsLeaf) ∧ SoundState (S 0)
          ∧ ¬ Monotone t
          ∧ (t i ≤ D ∧ v ∈ keys (S i))
          ∧ (D < t (j + 1) ∧ W ∈ S j
              ∧ W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))


/-- **MONOTONICITY BLOCKS IT.**  With `Monotone t` restored, the configuration
exhibited by `monotone_timestamps_indispensable` is impossible: no history from
a sound base admits both on-time delivery evidence and a deadline-pinned
reclaim witness for the same value.  Direct packaging of
`IMTAbstract.delivered_and_reclaimed_impossible` (cited, not re-proved) — the
exact statement whose hypothesis the counterexample above removes. -/
abbrev Properties.monotone_blocks_the_attack {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : SoundState (S 0)) (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {j : ℕ} {W : AbsLeaf} (hpin : D < t (j + 1)) (hW : W ∈ S j)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :=
  False


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
abbrev Properties.delivered_and_reclaimed_impossible_local {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    {i j : ℕ} (hloc : j + 1 ≤ i → t (j + 1) ≤ t i)
    (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {W : AbsLeaf} (hpin : D < t (j + 1)) (hW : W ∈ S j)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :=
  False


/-- Global monotonicity gives the local hypothesis for every index pair. -/
abbrev Properties.monotone_gives_local {t : ℕ → UInt256} (htmono : Monotone t) (i j : ℕ) :=
  j + 1 ≤ i → t (j + 1) ≤ t i


/-- **THE GLOBAL THEOREM IS A COROLLARY OF THE LOCAL ONE.**  Re-derives
`delivered_and_reclaimed_impossible`'s statement from
`delivered_and_reclaimed_impossible_local` via `monotone_gives_local`,
confirming the local hypothesis is a genuine weakening (nothing was lost). -/
abbrev Properties.delivered_and_reclaimed_impossible_of_local {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D v : UInt256}
    (hevo : Evolution S) (h0 : GapSound (S 0)) (hinj0 : KeyInj (S 0))
    (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (S i))
    {j : ℕ} {W : AbsLeaf} (hpin : D < t (j + 1)) (hW : W ∈ S j)
    (hlow : W.key < v) (hwin : W.nextKey = 0 ∨ v < W.nextKey) :=
  False


/-- **THE COUNTEREXAMPLE VIOLATES EXACTLY THE LOCAL CONDITION.**  For the
attack configuration of `monotone_timestamps_indispensable` (`i = 2`, `j = 0`),
the local hypothesis `j + 1 ≤ i → t (j+1) ≤ t i` fails: `1 ≤ 2` holds while
`attackTime a 1 = a > 0 = attackTime a 2`.  Together with
`delivered_and_reclaimed_impossible_local` this identifies the single inequality
about reported settlement times on which delivery/reclaim exclusivity rests. -/
abbrev Properties.attack_violates_local_hypothesis {a : UInt256} (ha : a ≠ 0) :=
  ¬ (0 + 1 ≤ 2 → attackTime a (0 + 1) ≤ attackTime a 2)


end AttackVectors.Timestamps
