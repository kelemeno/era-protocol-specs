import EraSpec.Contracts.IndexedMerkleTree.Specs.Model


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


end AttackVectors.Timestamps
