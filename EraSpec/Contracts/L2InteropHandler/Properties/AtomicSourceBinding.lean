import EraSpec.Contracts.L2InteropHandler.Specs.AtomicSourceBinding

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/-! Statements for `Specs/AtomicSourceBinding.lean`; its header gives the source at `b17415d20`. -/

namespace AttackVectors.AtomicSourceBinding


variable {Chain Value Hash : Type*}


/-! The pieces, named after the deployed quantities:

* `declared h` — the `sourceChainId` field of the bundle whose hash is `h`.  Taking it as a function
  of `h` presupposes that `bundleHash = keccak(bundleBytes)` (`IHB:231`) determines the field: the
  bytes carry it at bytes 64..96 (`InteropDataEncoding` topic `BundleHashAtV35`), but the hash half
  would be global keccak injectivity, which no map into `bytes32` has (topic `BundleHashPinned`).
* `commit h` — `commitValue(flowId, h)`, the value the IMT proof is checked against.
* `tree c` — chain `c`'s authenticated IMT leaf set. -/

variable (declared : Hash → Chain) (commit : Hash → Value) (tree : Chain → Set Value)


/-- **AS STATED, THIS IS ITS PREMISE INSTANTIATED.**  `HonestCommits declared commit tree` is
`∀ c h, commit h ∈ tree c → declared h = c`; applied to `c`, `h` and `hproof` it is the conclusion,
so nothing about the code is derived here, and `declared : Hash → Chain` presupposes that a bundle
hash determines its source chain.  The binding it is named after — the vouching chain, whose tree
holds the leg's commit value, is the chain the presented bytes declare, so the identity handed to the
recipient is one that chain's tree vouched for — was derived for the
interop pin `c67894b9` in the History topic `AtomicSourceBindingStrong`
(`History.Properties.AtomicSourceBoundToVouchingTreeOrLoggedClash`), from the decoded
`sourceChainId`, the destination's own hash computation and the honest insertion of the one tree,
up to the tree's sentinel and keccak collisions on named preimages.  The History topic
`SourceBindingReduced` derived it from the vouching chain's whole source run instead, with no premise on its tree
(`Contracts.SourceBinding.History.Properties.AtomicSourceBoundOrBreak`). -/
abbrev Properties.atomic_source_bound (hhc : HonestCommits declared commit tree)
    {c : Chain} {h : Hash} (hproof : commit h ∈ tree c) :=
  declared h = c


/-- **AND THAT IS THE WHOLE OF IT.**  Drop `HonestCommits` and the declared source is unconstrained:
a chain holding a foreign leg's commit value makes the vouching chain differ from the declared one,
and on the atomic path nothing else looks at the field — check (1) compares it to itself.

Under the stated threat model ("chains are not malicious") this configuration does not arise.  The
point is that it is the ONLY thing ruling it out here.  The witness is a two-point toy (`Bool`,
`Unit`) unrelated to the code: it shows only that `HonestCommits` is not trivially true.  The
configuration in the pin's code model is `History.Properties.ForeignCommitInTreeUnbindsSource`
(topic `AtomicSourceBindingStrong`, `c67894b9`). -/
abbrev Properties.atomic_source_unbound_without_honest :=
  ∃ (Chain Value Hash : Type) (declared : Hash → Chain) (commit : Hash → Value)
        (tree : Chain → Set Value) (c : Chain) (h : Hash),
        commit h ∈ tree c ∧ declared h ≠ c


/-- The vacuous check, stated so the asymmetry between the two paths is on the record: passing a
value to be compared against itself constrains nothing, whatever the value is.  (This is `x = x` for
any type; it does not model the validator or its call sites, which the
History topic `AtomicSourceBindingStrong` did at `c67894b9`.) -/
abbrev Properties.self_comparison_vacuous {α : Type*} (x : α) :=
  x = x


/-! ## The contrast, and why it is worth recording

| | public path | atomic path |
|---|---|---|
| `proofChainId` | chain of the L1 message inclusion proof | the bundle's own `sourceChainId` |
| check (1) | genuine cross-check | `x == x` |
| source binding | message proof AND the IMT argument | the IMT argument alone |
| survives a misbehaving chain in the leg set | the message proof still binds | nothing binds |

`ProofPolarity.inclusion_binding_requires_honesty` already showed the inclusion side loses its
self-binding without `HonestInsertion`.  What this file adds is the CONSEQUENCE at the point of use:
on the atomic path that self-binding is not defence in depth, it is the only depth there is, and the
value it protects is the caller identity presented to the recipient.

`LocalHonesty` is the mitigation and should be read alongside: `HonestInsertion` holds for any chain
running an unmodified deployment, enforced there by a three-link authorisation chain. So the residual
exposure is exactly a chain in the flow's leg set that is NOT running one — which the threat model
already excludes.  Recorded, not reported as a defect. -/

end AttackVectors.AtomicSourceBinding
