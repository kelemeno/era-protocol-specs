import EraSpec.Protocol.FlowAtomicityPerChain.Specs.Model

/-!
# Properties: flow atomicity with one commitment history per source chain

Statements about `EraSpec.Protocol.FlowAtomicityPerChain.Specs.Model`; proofs in
`EraSpec.Protocol.FlowAtomicityPerChain.Proofs.Model`.  Pure order theory over
`IMTAbstract` leaf sets, with no hash premise.

* `Properties.LegsPresentAtLaterSnapshotsPerChain` is
  `FlowAtomicity.executed_leg_executable_at_every_later_root` with each leg read in its own
  chain's history, at its own chain's snapshot index.
* `Properties.FlowOutcomeDichotomyPerChain` is `FlowAtomicity.flow_outcome_dichotomy` with
  each leg read in its own chain's history.  The reclaim witness is a leaf of that history:
  at `c67894b9` the deployed absence check also accepts the padding sentinel at an empty
  slot (the Correction (StaleSnapshotFaithful) note on `FlowAtomicity`'s header), so "never
  both" holds for genuine witnesses only.
* `Properties.SharedHistoryMisreadsTwoChainFlow` is the countermodel to the single-history
  reading, and the witness for both statements above.  In a two-chain flow whose legs are
  each committed on their own chain, chain `0`'s history (the one leg `(0, a)` is checked
  against) does not contain leg `(1, b)` and has a reclaim witness for it, and the two
  chains' histories differ.  So taking `FlowAtomicity`'s one `S` to be a chain's history
  classifies a leg committed on its own chain as reclaimable.  The deployed gates check
  each leg against its declared chain (Specs); the leg-to-chain binding is
  `Contracts.Protocol.Properties.unbound_gate_refunds_delivered_leg`.
-/

namespace AttackVectors.FlowAtomicityPerChain

open IMTAbstract

/-- **EVERY LEG STAYS PRESENT AT EVERY LATER SNAPSHOT OF ITS OWN CHAIN.**  If every chain's
history is an `Evolution` and every leg of the flow is a key of its own chain's snapshot
`n leg.chain`, then every leg is a key of every later snapshot of its own chain. -/
def Properties.LegsPresentAtLaterSnapshotsPerChain : Prop :=
  ∀ (S : ChainHistories), (∀ c, Evolution (S c)) →
    ∀ (flow : List ChainLeg) (n : UInt256 → ℕ),
      (∀ leg ∈ flow, leg.value ∈ keys (S leg.chain (n leg.chain))) →
        ∀ leg ∈ flow, ∀ j, n leg.chain ≤ j → leg.value ∈ keys (S leg.chain j)

/-- **ONE OUTCOME PER LEG, IN ITS OWN CHAIN'S LEAF SET.**  Along guarded histories from
genesis, every nonzero leg, at every snapshot `j leg.chain` of its own chain, is a key there
or has a leaf there whose window straddles it, and not both.  A statement about leaf sets:
it says nothing about which proofs a prover can present, and a padded-slot forgery is not a
leaf (module docstring). -/
def Properties.FlowOutcomeDichotomyPerChain : Prop :=
  ∀ (S : ChainHistories), (∀ c, GuardedEvolution (S c)) →
    (∀ c, S c 0 = ({⟨0, 0⟩} : Finset AbsLeaf)) →
    ∀ (flow : List ChainLeg), (∀ leg ∈ flow, leg.value ≠ 0) → ∀ (j : UInt256 → ℕ),
      ∀ leg ∈ flow,
        (leg.value ∈ keys (S leg.chain (j leg.chain))
            ∨ ∃ W ∈ S leg.chain (j leg.chain), W.key < leg.value
                ∧ (W.nextKey = 0 ∨ leg.value < W.nextKey))
          ∧ ¬ (leg.value ∈ keys (S leg.chain (j leg.chain))
            ∧ ∃ W ∈ S leg.chain (j leg.chain), W.key < leg.value
                ∧ (W.nextKey = 0 ∨ leg.value < W.nextKey))

/-- **ONE SHARED HISTORY MISREADS A TWO-CHAIN FLOW.**  For distinct nonzero `a, b`:
`twoChainHistories a b` is, chain by chain, a guarded `Evolution` from genesis; each leg of
`twoChainFlow a b` is a key of its own chain's snapshot 1; leg `b` is not a key of chain
`0`'s snapshot 1 and has a leaf there whose window straddles it; and chain `0`'s and chain
`1`'s histories differ.  Every premise of `LegsPresentAtLaterSnapshotsPerChain` (with
`n = fun _ => 1`) and of `FlowOutcomeDichotomyPerChain` holds on this instance. -/
def Properties.SharedHistoryMisreadsTwoChainFlow : Prop :=
  ∀ (a b : UInt256), a ≠ 0 → b ≠ 0 → a ≠ b →
    (∀ c, GuardedEvolution (twoChainHistories a b c) ∧ Evolution (twoChainHistories a b c)
        ∧ twoChainHistories a b c 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
      ∧ (∀ leg ∈ twoChainFlow a b, leg.value ≠ 0
          ∧ leg.value ∈ keys (twoChainHistories a b leg.chain 1))
      ∧ b ∉ keys (twoChainHistories a b 0 1)
      ∧ (∃ W ∈ twoChainHistories a b 0 1, W.key < b ∧ (W.nextKey = 0 ∨ b < W.nextKey))
      ∧ twoChainHistories a b 0 ≠ twoChainHistories a b 1

end AttackVectors.FlowAtomicityPerChain
