import EraSpec.Contracts.AtomicInteropProof.Specs.ProofPolarityStrong

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/-!
# Proof polarity, stated against the gates

`ProofPolarity` explains why `AtomicFlowManager`'s source-chain comparison is redundant on the
inclusion path and load-bearing on the refund path.  Its named statements, however, are
one-step consequences of `HonestInsertion`, and none of them mentions a gate:

* `absence_at_every_wrong_chain` is the same proposition as `inclusion_wrong_chain_impossible`.
* `finalized_leg_still_absent_elsewhere` returns its premise `hlive` as its first conjunct.
* `refund_blocked_when_chain_pinned` is `hlive` rewritten along `hpinned`.
* `polarity_summary` pairs `HonestInsertion` at `(c, v)` with its contrapositive.

Nothing there shows that the premises can hold together: honest insertion, a live leg, and a
second chain.

This file states the asymmetry against the gates of `Specs/ProofPolarityStrong.lean`, with
non-vacuity witnesses, and lifts it to commitment-tree states.

* **Refund path, with the check.**  `checked_absence_gate_rejects_live_leg` and
  `checked_absence_gate_iff_absent`: the deployed refund gate opens exactly for legs absent from
  their declared chain, whichever chain the prover names.
* **Inclusion path.**  `unchecked_inclusion_gate_iff_checked`: under honest insertion, deleting
  the comparison changes nothing; the two gates accept the same legs.
  `unchecked_inclusion_gate_differs_without_honesty`: without honest insertion they differ.
* **Refund path, without the check.**  `unchecked_absence_gate_iff` gives its exact acceptance
  set.  `unchecked_absence_gate_accepts_every_leg`: once two chains exist it accepts EVERY leg,
  so its verdict carries no information about the leg.
* **Both together.**  `polarity_asymmetry`: one hypothesis, opposite consequences, as gates.
* **The attack, non-vacuously.**  `finalized_leg_passes_unchecked_absence_gate` gives an honest
  model with a finalized leg that the unchecked refund gate accepts and the checked one rejects.
  `honest_polarity_model_exists` witnesses the premises of the universal statements, with a live
  leg and a missing leg.
* **On contract states.**  `chains_bound_gate_iff_checked_absence_gate` and
  `chains_unbound_gate_iff_unchecked_absence_gate`: on valid commitment trees and for nonzero
  values, `MultichainGate`'s IMT-level gates ARE these gates over `liveKeys T`.
  `chains_delivered_pins_source` and `chains_unbound_gate_accepts_every_leg` are the polarity on
  valid states: under honest insertion, a delivered value pins its chain, and the unbound gate
  accepts every nonzero value.  `chains_honest_double_mint_witness` shows the premises hold on
  real states, with a delivered leg that the unbound gate refunds.

The positive half on contract states, that the bound gate rejects a delivered leg, is
`Contracts.Protocol.bound_gate_excludes_delivered`.  It needs no honesty premise.

No hash premise appears in this file.  `HonestInsertion srcOf (liveKeys T)` is a premise about one
concrete family of states, and `chains_honest_double_mint_witness` shows it is satisfiable.
-/

namespace AttackVectors.ProofPolarity


section Abstract

variable {Chain Value : Type*}

variable (srcOf : Value → Chain)

variable (tree : Chain → Set Value)


/-! ## The refund gate with the comparison -/

/-- **THE CHECKED REFUND GATE REJECTS EVERY LIVE LEG.**  If a leg's value is in its own chain's
tree, the deployed refund gate, with the declared chain set to that chain, rejects it whatever
chain `c` the prover names.  If `c` is a different chain the comparison fails.  If `c` is the
leg's chain, the absence check fails.

This is the gate-level form of `refund_blocked_when_chain_pinned`.  It needs no
`HonestInsertion`.  Witness for the premise: `honest_polarity_model_exists`. -/
abbrev Properties.checked_absence_gate_rejects_live_leg {v : Value}
    (hlive : v ∈ tree (srcOf v)) :=
  ∀ c, ¬ CheckedAbsenceGate tree (srcOf v) c v


/-- **THE CHECKED REFUND GATE OPENS EXACTLY ON LEGS ABSENT FROM THEIR DECLARED CHAIN.**  Some
prover choice passes the deployed refund gate iff the value is absent from the declared chain's
tree.  The forward direction is safety and the reverse is liveness: an honest prover can always
refund a missing leg, by naming its declared chain. -/
abbrev Properties.checked_absence_gate_iff_absent (declared : Chain) (v : Value) :=
  (∃ c, CheckedAbsenceGate tree declared c v) ↔ v ∉ tree declared


/-! ## The inclusion path: the comparison is redundant under honest insertion -/

/-- **ON THE INCLUSION PATH THE COMPARISON CHANGES NOTHING.**  Under honest insertion, the
finality gate with the comparison deleted accepts exactly the legs that the deployed gate
accepts, when the declared chain is the leg's own chain.  A membership proof against any chain
already pins that chain.  This is the "defense-in-depth" label of `requireFlowFinalized`, as a
statement about the two gates.

Witness for the premise, with a leg each side accepts and one it rejects:
`honest_polarity_model_exists`. -/
abbrev Properties.unchecked_inclusion_gate_iff_checked (h : HonestInsertion srcOf tree) (v : Value) :=
  (∃ c, UncheckedInclusionGate tree c v) ↔ (∃ c, CheckedInclusionGate tree (srcOf v) c v)


/-! ## The refund path: without the comparison, absence is chain-blind -/

/-- **THE UNCHECKED REFUND GATE'S EXACT ACCEPTANCE SET.**  Under honest insertion, the refund
gate with the comparison deleted accepts `v` iff there is a chain other than `v`'s own, or `v`
is absent from its own chain's tree.  The first disjunct does not mention `v`'s status at all.

Witness for the premise: `honest_polarity_model_exists`. -/
abbrev Properties.unchecked_absence_gate_iff (h : HonestInsertion srcOf tree) (v : Value) :=
  (∃ c, UncheckedAbsenceGate tree c v) ↔ ((∃ c, c ≠ srcOf v) ∨ v ∉ tree (srcOf v))


/-- **ABSENCE IS CHAIN-BLIND: WITH TWO CHAINS, THE UNCHECKED REFUND GATE ACCEPTS EVERY LEG.**
Under honest insertion, as soon as two distinct chains exist, every value has an absence proof
at a chain other than its own.  So the unchecked refund gate accepts every leg, finalized or
not.  On the refund path the comparison is therefore the ONLY thing that ties the proof to the
leg's status.

Witness for the premises: `honest_polarity_model_exists`. -/
abbrev Properties.unchecked_absence_gate_accepts_every_leg (h : HonestInsertion srcOf tree)
    {c₀ c₁ : Chain} (hne : c₀ ≠ c₁) :=
  ∀ v, ∃ c, c ≠ srcOf v ∧ UncheckedAbsenceGate tree c v


/-- **THE ASYMMETRY, AS GATES: ONE HYPOTHESIS, OPPOSITE CONSEQUENCES.**  Under honest insertion
and two distinct chains:

* on the inclusion path, deleting the comparison changes nothing: the two finality gates accept
  the same legs;
* on the refund path, deleting it changes everything: for every live leg, the unchecked refund
  gate accepts while the deployed one rejects.

Witness for the premises, with a live leg: `honest_polarity_model_exists`. -/
abbrev Properties.polarity_asymmetry (h : HonestInsertion srcOf tree)
    {c₀ c₁ : Chain} (hne : c₀ ≠ c₁) :=
  (∀ v, (∃ c, UncheckedInclusionGate tree c v) ↔ (∃ c, CheckedInclusionGate tree (srcOf v) c v)) ∧
    (∀ v, v ∈ tree (srcOf v) →
      (∃ c, UncheckedAbsenceGate tree c v) ∧ ¬ ∃ c, CheckedAbsenceGate tree (srcOf v) c v)

end Abstract


/-! ## Non-vacuity, and the role of honesty -/

/-- **THE ATTACK THE CHECK BLOCKS, NON-VACUOUSLY.**  There is a model with honest insertion and
a leg that FINALIZED: the deployed finality gate accepts it against its own chain.  The refund
gate with the comparison deleted accepts the same leg against another chain, which is the
double-mint.  The deployed refund gate rejects it for every chain the prover names.

This is the satisfiable form of `finalized_leg_still_absent_elsewhere`, stated against the
gates.  The same attack on commitment-tree states is
`chains_honest_double_mint_witness` (and `Contracts.Protocol.chains_unbound_gate_refunds_delivered_leg`). -/
abbrev Properties.finalized_leg_passes_unchecked_absence_gate :=
  ∃ (Chain Value : Type) (srcOf : Value → Chain) (tree : Chain → Set Value) (v : Value) (c : Chain),
    HonestInsertion srcOf tree ∧
      CheckedInclusionGate tree (srcOf v) (srcOf v) v ∧
      UncheckedAbsenceGate tree c v ∧
      ¬ ∃ c', CheckedAbsenceGate tree (srcOf v) c' v


/-- **ANTI-VACUITY FOR THE UNIVERSAL STATEMENTS.**  The premises of
`checked_absence_gate_rejects_live_leg`, `unchecked_inclusion_gate_iff_checked`,
`unchecked_absence_gate_iff`, `unchecked_absence_gate_accepts_every_leg` and
`polarity_asymmetry` hold together.  The model has honest insertion, two distinct chains, a live
leg `v` and a missing leg `w`.  So `unchecked_inclusion_gate_iff_checked` and
`checked_absence_gate_iff_absent` are exercised on both sides (true at `v` and false at `w`, or the
reverse).  `unchecked_absence_gate_iff` is not: once two chains exist both of its sides hold for
every value, which is the point of `unchecked_absence_gate_accepts_every_leg`. -/
abbrev Properties.honest_polarity_model_exists :=
  ∃ (Chain Value : Type) (srcOf : Value → Chain) (tree : Chain → Set Value) (c₀ c₁ : Chain)
      (v w : Value),
    HonestInsertion srcOf tree ∧ c₀ ≠ c₁ ∧ v ∈ tree (srcOf v) ∧ w ∉ tree (srcOf w)


/-- **WITHOUT HONEST INSERTION, THE TWO FINALITY GATES DIFFER.**  A chain that holds a foreign
leg's value lets the finality gate with the comparison deleted accept a leg that the deployed
gate rejects, because the leg never committed on its own chain.  So the redundancy in
`unchecked_inclusion_gate_iff_checked` rests on honest insertion: a single foreign value in a single
chain's tree is enough to break it.  The witness places no constraint on `tree` beyond that, so it
does not say which chains must be honest.  This is the gate-level form of
`inclusion_binding_requires_honesty`. -/
abbrev Properties.unchecked_inclusion_gate_differs_without_honesty :=
  ∃ (Chain Value : Type) (srcOf : Value → Chain) (tree : Chain → Set Value) (v : Value),
    (∃ c, UncheckedInclusionGate tree c v) ∧ ¬ ∃ c, CheckedInclusionGate tree (srcOf v) c v


/-! ## On commitment-tree states

The abstract trees are `liveKeys T` for a family `T` of `L2InteropCommitmentTree` states.  Only
the chains a statement names are assumed valid.  `v ≠ 0` excludes the sentinel, which is a key
of every valid tree. -/

/-- **INCLUSION SELF-BINDS ON CONTRACT STATES.**  Under honest insertion over the trees' nonzero
keys, a nonzero value delivered on chain `c` (a key of `c`'s commitment tree, as
`Contracts.Protocol.Delivered` reads it) originates on `c`.

Witness for the premises, with the value delivered: `chains_honest_double_mint_witness`. -/
abbrev Properties.chains_delivered_pins_source
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    {srcOf : UInt256 → Contracts.Protocol.Chain} (h : HonestInsertion srcOf (liveKeys T))
    {c : Contracts.Protocol.Chain} {v : UInt256} (hv : v ≠ 0)
    (hdel : Contracts.Protocol.Delivered (Contracts.Protocol.ofChains T) c v) :=
  srcOf v = c


/-- **THE CHECKED ABSENCE GATE IS THE CONTRACT-LEVEL BOUND GATE.**  For a valid commitment tree
on the declared chain and a nonzero value, `MultichainGate`'s bound gate (an IMT low leaf of the
declared chain's tree whose window straddles `v`) accepts iff the checked absence gate over
`liveKeys T` accepts.

Witness for the premises: `chains_honest_double_mint_witness`.  On that state both sides are
false at the source chain (`¬ BoundGate`) and true at some other chain (`UnboundGate`). -/
abbrev Properties.chains_bound_gate_iff_checked_absence_gate
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    {src : Contracts.Protocol.Chain} (hV : Contracts.InteropCommitmentTree.Valid (T src))
    {v : UInt256} (hv : v ≠ 0) :=
  Contracts.Protocol.BoundGate (Contracts.Protocol.ofChains T) src v ↔
    ∃ c, CheckedAbsenceGate (liveKeys T) src c v


/-- **THE UNCHECKED ABSENCE GATE IS THE CONTRACT-LEVEL UNBOUND GATE.**  If every chain's
commitment tree is valid and the value is nonzero, `MultichainGate`'s unbound gate accepts iff
the unchecked absence gate over `liveKeys T` accepts for some chain.

Witness for the premises: `chains_honest_double_mint_witness`. -/
abbrev Properties.chains_unbound_gate_iff_unchecked_absence_gate
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    (hV : ∀ c, Contracts.InteropCommitmentTree.Valid (T c)) {v : UInt256} (hv : v ≠ 0) :=
  Contracts.Protocol.UnboundGate (Contracts.Protocol.ofChains T) v ↔
    ∃ c, UncheckedAbsenceGate (liveKeys T) c v


/-- **ON CONTRACT STATES, THE UNBOUND GATE ACCEPTS EVERY NONZERO LEG.**  If every chain's
commitment tree is valid and insertion is honest, every nonzero commit value, delivered or not,
has a genuine IMT non-inclusion witness in the tree of a chain other than its own.  So the
refund gate without `authorizeRefund`'s comparison accepts every leg.  This is the contract-level
form of `unchecked_absence_gate_accepts_every_leg`.

Witness for the premises, with the value delivered on its own chain:
`chains_honest_double_mint_witness`. -/
abbrev Properties.chains_unbound_gate_accepts_every_leg
    {T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree}
    (hV : ∀ c, Contracts.InteropCommitmentTree.Valid (T c))
    {srcOf : UInt256 → Contracts.Protocol.Chain} (h : HonestInsertion srcOf (liveKeys T))
    {v : UInt256} (hv : v ≠ 0) :=
  ∃ c, c ≠ srcOf v ∧ Contracts.Protocol.BoundGate (Contracts.Protocol.ofChains T) c v


/-- **THE DOUBLE-MINT ON HONEST CONTRACT STATES.**  There is a family of commitment-tree states
with every chain valid and insertion honest.  On it a nonzero value is delivered on its own
source chain, the unbound gate accepts it, and the bound gate for its source chain rejects it.
The proof uses `Contracts.Protocol.attackChains`: `setup` on every chain, then one guarded
`insert` on chain `0`.

This witnesses the premises of every contract-level statement above.  Unlike
`Contracts.Protocol.chains_unbound_gate_refunds_delivered_leg`, it also shows that honest
insertion holds there. -/
abbrev Properties.chains_honest_double_mint_witness :=
  ∃ (T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree)
      (srcOf : UInt256 → Contracts.Protocol.Chain) (v : UInt256),
    (∀ c, Contracts.InteropCommitmentTree.Valid (T c)) ∧ HonestInsertion srcOf (liveKeys T) ∧
      v ≠ 0 ∧
      Contracts.Protocol.Delivered (Contracts.Protocol.ofChains T) (srcOf v) v ∧
      Contracts.Protocol.UnboundGate (Contracts.Protocol.ofChains T) v ∧
      ¬ Contracts.Protocol.BoundGate (Contracts.Protocol.ofChains T) (srcOf v) v


end AttackVectors.ProofPolarity
