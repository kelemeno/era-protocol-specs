import Mathlib.Tactic

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

/-- **THE IMPLICIT ASSUMPTION.**  Every chain's tree holds only the commit values of legs that
originate on that chain.  This is what an honest `AtomicFlowManager` guarantees for its OWN chain: it
inserts `commitValue(flowId, bundleHash)` only for bundles it originated.  As a statement about ALL
chains it is an assumption about every chain in the flow's leg set. -/
def HonestInsertion : Prop := ∀ c v, v ∈ tree c → srcOf v = c

/-! ## Positive polarity: inclusion carries its own chain binding -/

/-- **INCLUSION SELF-BINDS.**  A membership witness already determines the chain, so the explicit
equality check adds nothing on this path — the "defense-in-depth" reading. -/
theorem inclusion_self_binds (h : HonestInsertion srcOf tree) {c : Chain} {v : Value}
    (hmem : v ∈ tree c) : srcOf v = c := h c v hmem

/-- Equivalently: a proof against the wrong chain's root cannot be produced at all. -/
theorem inclusion_wrong_chain_impossible (h : HonestInsertion srcOf tree) {c : Chain} {v : Value}
    (hne : srcOf v ≠ c) : v ∉ tree c := fun hmem => hne (h c v hmem)

/-! ## Negative polarity: absence carries NO chain binding

The reversal is immediate, and it is the same hypothesis being used.  Under honest insertion a leg's
value is missing from every foreign tree — so an absence witness is available at every wrong chain, for
free, no matter what the leg actually did. -/

/-- **ABSENCE IS CHAIN-BLIND.**  The very assumption that made inclusion self-binding hands an absence
witness to every wrong chain.  So on the refund path the explicit check is the ONLY thing tying the
proof to the leg's chain. -/
theorem absence_at_every_wrong_chain (h : HonestInsertion srcOf tree) {c : Chain} {v : Value}
    (hne : srcOf v ≠ c) : v ∉ tree c := inclusion_wrong_chain_impossible srcOf tree h hne

/-- **THE ATTACK THE CHECK BLOCKS.**  A leg that is committed and finalized on its own chain — the
strongest possible evidence that it must NOT be refunded — still admits an absence witness at every
other chain.  Without the equality check, `authorizeRefund` would accept one, marking a live leg
`Revertable`: the double-mint the source comment names. -/
theorem finalized_leg_still_absent_elsewhere (h : HonestInsertion srcOf tree)
    {v : Value} {c : Chain} (hlive : v ∈ tree (srcOf v)) (hne : srcOf v ≠ c) :
    v ∈ tree (srcOf v) ∧ v ∉ tree c :=
  ⟨hlive, absence_at_every_wrong_chain srcOf tree h hne⟩

/-- **THE CHECK RESTORES SOUNDNESS.**  With the proof's chain pinned to the leg's declared chain, a
committed leg leaves no absence witness — the refund gate cannot pass. -/
theorem refund_blocked_when_chain_pinned {v : Value} {c : Chain}
    (hpinned : c = srcOf v) (hlive : v ∈ tree (srcOf v)) : v ∈ tree c := by
  rw [hpinned]; exact hlive

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
theorem inclusion_binding_requires_honesty :
    ∃ (Chain Value : Type) (srcOf : Value → Chain) (tree : Chain → Set Value) (c : Chain) (v : Value),
      v ∈ tree c ∧ srcOf v ≠ c := by
  refine ⟨Bool, Unit, fun _ => true, fun _ => Set.univ, false, (), ?_, ?_⟩
  · exact Set.mem_univ _
  · exact Bool.noConfusion

/-- The two paths, side by side: one hypothesis, opposite consequences.  This is the whole content of
the asymmetry, and it is why no amount of care in `commitValue` could have removed the refund-path
check — the binding is not missing there, it is unavailable in principle to a negative property. -/
theorem polarity_summary (h : HonestInsertion srcOf tree) {v : Value} {c : Chain} (hne : srcOf v ≠ c) :
    (v ∈ tree c → srcOf v = c) ∧ v ∉ tree c :=
  ⟨fun hmem => h c v hmem, absence_at_every_wrong_chain srcOf tree h hne⟩

end AttackVectors.ProofPolarity
