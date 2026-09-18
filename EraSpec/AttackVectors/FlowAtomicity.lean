import EraSpec.Core.IMT

/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/FlowAtomicity.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ATTACK VECTOR: MULTI-LEG / PARTIAL-EXECUTION IMBALANCE.

  A cross-chain flow is a finite collection of legs, each identified by its
  commit value (here: a `List UInt256`).  All legs of a flow share ONE
  commitment history `S` — the interop roots are published to every chain,
  so every chain of the flow verifies its legs against snapshots of the
  same evolving key set.

  The attack: force a state where one leg is irreversibly executed while a
  sibling leg is permanently stuck (no delivery evidence AND no reclaim
  witness) or double-paid (delivered AND refundable) — extracting value
  from the imbalance between the legs.

  SANCTIONED ATOMICITY INTERPRETATION (this project's settled reading):
  atomicity means the CROSS-CHAIN guarantee "executed on one chain ⟹
  executable on all chains" — delivery evidence for a leg, once accepted
  anywhere, remains verifiable against every later published root, so no
  sibling chain can ever find that leg missing.  Atomicity does NOT mean
  single-chain all-or-nothing delivery of the whole flow, and nothing here
  claims it.

  What this file establishes:

  * `leg_evidence_never_decays` — delivery evidence for a leg of the flow
    never decays: once the leg's commit value is a key of snapshot `i`, it
    is a key of EVERY snapshot `j ≥ i`.  Any chain verifying against any
    later published root accepts the same leg.

  * `executed_leg_executable_at_every_later_root` — the atomicity property
    in the sanctioned sense, at flow level: once ALL legs of the flow are
    delivered by snapshot `n`, every leg is present at every snapshot
    `≥ n` — a sibling chain verifying later cannot find any leg missing.

  * `no_leg_both_executed_and_refundable` — no leg of the flow can be
    simultaneously delivered on time (`t i ≤ D`, `v ∈ keys (S i)`) and
    carry a reclaim witness at a deadline-pinned snapshot (`D < t (j+1)`):
    the "one leg executed, sibling refunded, then executed leg ALSO
    refunded" double-extraction is impossible, leg by leg.

  * `flow_outcome_dichotomy` — every nonzero leg of the flow, at every
    snapshot `j` (in particular at the deadline-pinned snapshot the
    reclaim gate evaluates), is either delivered (`v ∈ keys (S j)`) or
    reclaimable (a straddling gap witness exists in `S j`) — and NEVER
    both.  Each leg individually has exactly one outcome: no leg is ever
    permanently stuck, and no leg is ever double-paid.

  HONEST LIMITATION — MIXED OUTCOMES ARE PERMITTED AT THIS LAYER: the
  abstract layer does NOT prove that all legs of a flow reach the SAME
  outcome.  That would be all-or-nothing delivery, which is NOT the
  sanctioned atomicity interpretation and is NOT true here: the model
  permits some legs of a flow to be delivered while sibling legs time out
  and are refunded.  This is formalized, not just stated:

  * `mixed_outcomes_permitted` — an explicit `GuardedEvolution` from the
    genesis singleton and a two-leg flow `[a, b]` in which leg `a` is
    delivered at snapshot 1 while leg `b` is absent there AND carries a
    valid reclaim witness — one leg executed, the sibling refundable, in a
    perfectly sound history.  Whatever forces same-outcome (if anything)
    must live in the higher-level bundle/executor logic, not in the
    commitment tree.

  Pure order theory over `IMTAbstract` — axiom-free, no EVM semantics.
-/

namespace AttackVectors.FlowAtomicity

open IMTAbstract
open Clear

/-- **LEG EVIDENCE NEVER DECAYS.**  If leg `v` of the flow is delivered at
snapshot `i` (its commit value is a key of `S i`), then `v` is a key of
EVERY later snapshot `j ≥ i`: any chain verifying against ANY later
published root accepts the same leg.  Direct flow-level packaging of
`evolution_keys_mono`. -/
theorem leg_evidence_never_decays
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S)
    (flow : List UInt256) {v : UInt256} (_hleg : v ∈ flow)
    {i : ℕ} (hdel : v ∈ keys (S i)) :
    ∀ j, i ≤ j → v ∈ keys (S j) :=
  fun _ hij => evolution_keys_mono hevo hij hdel

/-- **EXECUTED ON ONE ⟹ EXECUTABLE ON ALL (the sanctioned atomicity).**
For a flow whose legs are ALL delivered by snapshot `n`, every leg is
present at every snapshot `≥ n`.  A sibling chain verifying any leg of the
flow against any later published root cannot find it missing — execution
of the flow anywhere guarantees executability of every leg everywhere,
forever after. -/
theorem executed_leg_executable_at_every_later_root
    {S : ℕ → Finset AbsLeaf} (hevo : Evolution S)
    (flow : List UInt256) {n : ℕ}
    (hall : ∀ v ∈ flow, v ∈ keys (S n)) :
    ∀ j, n ≤ j → ∀ v ∈ flow, v ∈ keys (S j) :=
  fun _ hnj v hv => evolution_keys_mono hevo hnj (hall v hv)

/-- **NO LEG IS BOTH EXECUTED AND REFUNDABLE.**  Along a guarded history
from genesis with monotone settlement timestamps, no leg of the flow can
simultaneously carry on-time delivery evidence (`t i ≤ D` and
`v ∈ keys (S i)`) and a deadline-pinned reclaim witness (`D < t (j+1)`,
straddling leaf `W ∈ S j`).  The double-extraction where an executed leg is
also refunded is impossible for every leg of the flow. -/
theorem no_leg_both_executed_and_refundable
    {S : ℕ → Finset AbsLeaf} {t : ℕ → UInt256} {D : UInt256}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (htmono : Monotone t) (flow : List UInt256) :
    ∀ v ∈ flow, ∀ i j : ℕ, ∀ W : AbsLeaf,
      t i ≤ D → v ∈ keys (S i) →
      D < t (j+1) → W ∈ S j → W.key < v →
      ¬ (W.nextKey = 0 ∨ v < W.nextKey) := by
  intro v _ i j W hti hdel htj1 hW hlow
  exact (guardedEvolution_delivered_available_forever hge hgen htmono
    hti hdel).2 j W htj1 hW hlow

/-- **FLOW OUTCOME DICHOTOMY (the honest flow-level statement).**  Along a
guarded history from genesis, EVERY nonzero leg of the flow, at every
snapshot `j` — in particular at the deadline-pinned snapshot the reclaim
gate evaluates — is either delivered (its commit value is a key of `S j`)
or reclaimable (some leaf of `S j` carries a window straddling it), and
NEVER both.  Each leg individually has exactly one outcome; the layer does
NOT force different legs to the same outcome (see
`mixed_outcomes_permitted`). -/
theorem flow_outcome_dichotomy
    {S : ℕ → Finset AbsLeaf}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (flow : List UInt256) (hnz : ∀ v ∈ flow, v ≠ 0) (j : ℕ) :
    ∀ v ∈ flow,
      (v ∈ keys (S j) ∨ ∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ∧ ¬ (v ∈ keys (S j)
              ∧ ∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)) := by
  intro v hv
  have hiff := guardedEvolution_reclaimable_iff_absent hge hgen
    (j := j) (hnz v hv)
  constructor
  · by_cases hmem : v ∈ keys (S j)
    · exact Or.inl hmem
    · exact Or.inr (hiff.mpr hmem)
  · rintro ⟨hmem, hwit⟩
    exact hiff.mp hwit hmem

/-- **MIXED OUTCOMES ARE PERMITTED — the sharpness witness.**  For any
distinct nonzero commit values `a, b` (the two legs of the flow `[a, b]`),
there is a `GuardedEvolution` from the genesis singleton in which, at
snapshot 1, leg `a` is DELIVERED while leg `b` is ABSENT and carries a
valid RECLAIM witness.  The abstract commitment-tree layer therefore does
NOT enforce same-outcome across the legs of a flow: "all legs delivered or
all legs refunded" is not a theorem of this layer, and any such guarantee
must come from higher-level bundle/executor logic.  (History: one guarded
insert of `a` at step 0, constant thereafter.) -/
theorem mixed_outcomes_permitted
    {a b : UInt256} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ S : ℕ → Finset AbsLeaf,
      GuardedEvolution S
        ∧ S 0 = ({⟨0, 0⟩} : Finset AbsLeaf)
        ∧ a ∈ [a, b] ∧ b ∈ [a, b]
        ∧ a ∈ keys (S 1)
        ∧ b ∉ keys (S 1)
        ∧ ∃ W ∈ S 1, W.key < b ∧ (W.nextKey = 0 ∨ b < W.nextKey) := by
  classical
  let S : ℕ → Finset AbsLeaf :=
    fun m => if m = 0 then ({⟨0, 0⟩} : Finset AbsLeaf)
             else imtInsert {⟨0, 0⟩} ⟨0, 0⟩ a
  have hS0 : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf) := rfl
  have hS1 : ∀ k : ℕ, S (k+1) = imtInsert {⟨0, 0⟩} ⟨0, 0⟩ a := fun _ => rfl
  have hzero_mem : (⟨0, 0⟩ : AbsLeaf) ∈ ({⟨0, 0⟩} : Finset AbsLeaf) :=
    Finset.mem_singleton_self _
  have hapos : (0 : UInt256) < a := Fin.pos_of_ne_zero ha
  have hanot : a ∉ keys ({⟨0, 0⟩} : Finset AbsLeaf) := by
    intro hmem
    obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_singleton] at hL
    rw [hL] at hLkey
    exact ha hLkey.symm
  have hge : GuardedEvolution S := by
    intro n
    cases n with
    | zero =>
      right
      refine ⟨⟨0, 0⟩, a, ?_, hapos, Or.inl rfl, ?_, ?_⟩
      · rw [hS0]; exact hzero_mem
      · rw [hS0]; exact hanot
      · rw [hS1 0, hS0]
    | succ k =>
      left
      rw [hS1 (k+1), hS1 k]
  have hdel : a ∈ keys (S 1) := by
    rw [hS1 0]
    exact imtInsert_key_mem hzero_mem
  have habs : b ∉ keys (S 1) := by
    rw [hS1 0]
    intro hmem
    rcases (mem_keys_imtInsert hzero_mem).mp hmem with heq | hmem0
    · exact hab heq.symm
    · obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hmem0
      rw [Finset.mem_singleton] at hL
      rw [hL] at hLkey
      exact hb hLkey.symm
  exact ⟨S, hge, hS0, by simp, by simp, hdel, habs,
    (guardedEvolution_reclaimable_iff_absent hge hS0 hb).mpr habs⟩

end AttackVectors.FlowAtomicity
