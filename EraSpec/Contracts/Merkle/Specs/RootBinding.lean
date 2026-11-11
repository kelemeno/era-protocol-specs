import EraSpec.Contracts.FullMerkle.Specs.Model


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/RootBinding.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ROOT BINDING — the abstract kernel of the last remaining obligation.

  `AttackVectors.CrossContract` reduced delivered-XOR-reclaimed to one hypothesis,
  `habs`: that every leaf committed under a published root really is a member of
  the represented leaf set.  That is ROOT BINDING, and it is the last real gap in
  the no-theft chain.

  Root binding factors into three pieces:

    (1) ABSTRACT KERNEL — equal roots force equal leaf lists, so membership
        transfers between any two lists sharing a root.  Proved here from
        `MerkleSpec.rootOf_inj_of_h_inj'` (M-D without its spurious nonemptiness
        hypothesis), with node-hash pair-injectivity as a HYPOTHESIS standing in for
        keccak collision resistance.  Since `hne` is gone these apply at an EMPTY
        tree too, which matters for instantiating them at genesis.
    (2) FOLD CORRESPONDENCE — the contract's `foldRoot` path recomputation agrees
        with `MerkleSpec.rootOf` on the same leaves.  NOT proved; this is the
        root-fidelity track (`ROOT_FIDELITY_BLUEPRINT.md` R0–R9), of which only the
        pure Merkle layer M-A/M-B/M-C/M-D exists.
    (3) SET CORRESPONDENCE — the leaf LIST the Merkle layer talks about and the
        leaf SET `leafSetOf` talks about are the same leaves.  NOT proved.

  Only (1) is established here.  Stating it separately is worth doing anyway: it
  shows the cryptographic content of root binding is exactly M-D, and that (2) and
  (3) are model-correspondence work rather than further cryptography.
-/

namespace AttackVectors.RootBinding


open Clear MerkleSpec


end AttackVectors.RootBinding
