import EraSpec.Contracts.AtomicInteropProof.Specs.ProofPolarity

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/ProofPolarity.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  PROOF POLARITY — why the same check is redundant for inclusion and load-bearing for absence.

  `AtomicFlowManager` applies ONE syntactic check on both paths:

      if (_finality.proofs[i].sourceChainId != flow.legSourceChainIds[i]) revert ProofSourceChainMismatch(...);
      if (_absence.sourceChainId != missingLegChainId)                    revert ProofSourceChainMismatch(...);

  and labels the two uses differently, on purpose:

      requireFlowFinalized: "defense-in-depth here (membership already self-binds via the
                             chain-specific `commitValue`) but load-bearing for the symmetric refund path"

      authorizeRefund:      "Without this, the leg's commit value -- which exists only in its own source
                             chain's tree -- is trivially absent from any other chain's tree, so an
                             on-time, finalized leg could be force-refunded against an unrelated chain
                             (double-mint)."

  Those comments are correct, and the asymmetry is not incidental to this codebase -- it follows from
  the POLARITY of the two properties.  This file proves that, and then sharpens the "defense-in-depth"
  label, which holds only under an assumption about OTHER chains that the comment leaves implicit.

  The pleasing part, and the reason it is worth writing down: the SAME assumption that makes inclusion
  self-binding is exactly what makes absence chain-blind.  One hypothesis, opposite consequences.

  Scope note.  The named statements below are the SET-LEVEL consequences of `HonestInsertion`
  (`v ∈ tree c`, `v ∉ tree c`).  Each is a one-step use of a premise, and none mentions a gate.  The
  asymmetry stated against the gates is in `ProofPolarityStrong`: the finality and refund gates with
  and without the comparison.  That module adds non-vacuity witnesses and lifts the statements to
  commitment-tree states (`liveKeys`, `Contracts.Protocol.BoundGate` / `UnboundGate`).
-/

namespace AttackVectors.ProofPolarity


variable {Chain Value : Type*}


/-! `srcOf v` — the source chain baked into a commit value.  Concretely
`commitValue = keccak(TAG, flowId, bundleHash)` and `bundleHash = keccak(sourceChainId, bundle)`, so
the chain is recoverable from the value; `BundleHashEncoding.abiEncode_inj` closes the encoding half of
that, and keccak injectivity the other.  Here it is simply a function, since only its existence matters. -/

variable (srcOf : Value → Chain)


/-! `tree c` — the leaf set of chain `c`'s IMT. -/

variable (tree : Chain → Set Value)


/-! ## Positive polarity: inclusion carries its own chain binding -/

/-- **INCLUSION SELF-BINDS.**  A membership witness already determines the chain, so the explicit
equality check adds nothing on this path — the "defense-in-depth" reading. -/
abbrev Properties.inclusion_self_binds (h : HonestInsertion srcOf tree) {c : Chain} {v : Value}
    (hmem : v ∈ tree c) :=
  srcOf v = c


/-- Equivalently: a proof against the wrong chain's root cannot be produced at all. -/
abbrev Properties.inclusion_wrong_chain_impossible (h : HonestInsertion srcOf tree) {c : Chain} {v : Value}
    (hne : srcOf v ≠ c) :=
  v ∉ tree c


/-! ## Negative polarity: absence carries NO chain binding

The reversal is immediate, and it is the same hypothesis being used.  Under honest insertion a leg's
value is missing from every foreign tree — so an absence witness is available at every wrong chain, for
free, no matter what the leg actually did. -/

/-- **ABSENCE AT A WRONG CHAIN (set form).**  The assumption that makes inclusion self-binding also
means that, under honest insertion, a leg's value is absent from every chain other than its own.  So an
absence witness is available there.

As a proposition this is IDENTICAL to `inclusion_wrong_chain_impossible`: both are the contrapositive of
`HonestInsertion` at `(c, v)`.  On its own it therefore does not express the asymmetry between the two
paths, and it says nothing about the refund gate.  The gate-level statements are in
`Properties/ProofPolarityStrong.lean`:
* `unchecked_absence_gate_accepts_every_leg`: once two chains exist, the refund gate without the
  comparison accepts EVERY leg.
* `unchecked_absence_gate_iff`: that gate's exact acceptance set.
* `checked_absence_gate_iff_absent`: the deployed gate opens exactly on legs absent from their declared
  chain. -/
abbrev Properties.absence_at_every_wrong_chain (h : HonestInsertion srcOf tree) {c : Chain} {v : Value}
    (hne : srcOf v ≠ c) :=
  v ∉ tree c


/-- **THE ATTACK THE CHECK BLOCKS (set form).**  A leg committed on its own chain still has its value
absent from every other chain's tree.  That is the double-mint the source comment names: without the
equality check, `authorizeRefund` would accept an absence proof from such a chain and mark a live leg
`Revertable`.

As stated, though, the first conjunct is the premise `hlive` returned unchanged.  The second is
`absence_at_every_wrong_chain`, which does not use `hlive`.  No refund gate appears, and nothing here
shows that the premises (honest insertion, a live leg, a second chain) can hold together.
* Against a modelled gate, the attack is `finalized_leg_passes_unchecked_absence_gate` in
  `Properties/ProofPolarityStrong.lean`.  It gives an honest model in which a finalized leg passes the
  refund gate without the comparison and fails the deployed one.
* On commitment-tree states, it is `chains_honest_double_mint_witness` there, and
  `Contracts.Protocol.chains_unbound_gate_refunds_delivered_leg`. -/
abbrev Properties.finalized_leg_still_absent_elsewhere (h : HonestInsertion srcOf tree)
    {v : Value} {c : Chain} (hlive : v ∈ tree (srcOf v)) (hne : srcOf v ≠ c) :=
  v ∈ tree (srcOf v) ∧ v ∉ tree c


/-- **PINNING THE CHAIN (set form).**  With the proof's chain pinned to the leg's own chain, a committed
leg's value is in that chain's tree.

As stated, this is `hlive` rewritten along `hpinned`.  It mentions no refund gate and no absence
predicate, so it does not by itself say that the refund gate cannot pass.  That statement is elsewhere:
* `checked_absence_gate_rejects_live_leg` in `Properties/ProofPolarityStrong.lean`: the deployed refund
  gate rejects a live leg whatever chain the prover names.  `checked_absence_gate_iff_absent` there is
  the exact form.
* On commitment-tree states, `Contracts.Protocol.bound_gate_excludes_delivered`, with
  `chains_bound_gate_iff_checked_absence_gate` identifying the two gates. -/
abbrev Properties.refund_blocked_when_chain_pinned {v : Value} {c : Chain}
    (hpinned : c = srcOf v) (hlive : v ∈ tree (srcOf v)) :=
  v ∈ tree c


/-! ## Sharpening the "defense-in-depth" label

`inclusion_self_binds` needs `HonestInsertion` — a statement about EVERY chain in the leg set, not just
the one running the code.  A chain that inserts a foreign leg's commit value into its own tree breaks
it, and nothing in this contract can prevent that: the foreign chain's IMT is its own.  So the label
is accurate under honest insertion and only then; drop the assumption and the check is load-bearing on
BOTH paths.  This is not a defect — the check is present — but it does mean the two paths rest on
different amounts of trust, which the comment does not say. -/

/-- **WITHOUT HONEST INSERTION, INCLUSION DOES NOT SELF-BIND.**  A misbehaving chain can hold a foreign
leg's commit value, so a membership witness exists against the wrong chain and the explicit equality
check becomes the only barrier on the inclusion path too. -/
abbrev Properties.inclusion_binding_requires_honesty :=
  ∃ (Chain Value : Type) (srcOf : Value → Chain) (tree : Chain → Set Value) (c : Chain) (v : Value),
        v ∈ tree c ∧ srcOf v ≠ c


/-- The two paths, side by side, as set facts.

As stated, both conjuncts are one fact about one chain: `HonestInsertion` at `(c, v)` and its
contrapositive under `hne`.  Once `v ∉ tree c` holds, the first conjunct is vacuous at `c`, and there is
no live-leg premise.  So this is not the whole content of the asymmetry.

The asymmetry as a statement about the two gates is `polarity_asymmetry` in
`Properties/ProofPolarityStrong.lean`.  Dropping the comparison changes nothing on the inclusion path,
and on every live leg it flips the refund verdict.  `honest_polarity_model_exists` there shows the
premises hold.  That asymmetry is why no amount of care in `commitValue` could have removed the
refund-path check: once two chains exist, the refund gate without it accepts every leg. -/
abbrev Properties.polarity_summary (h : HonestInsertion srcOf tree) {v : Value} {c : Chain} (hne : srcOf v ≠ c) :=
  (v ∈ tree c → srcOf v = c) ∧ v ∉ tree c


end AttackVectors.ProofPolarity
