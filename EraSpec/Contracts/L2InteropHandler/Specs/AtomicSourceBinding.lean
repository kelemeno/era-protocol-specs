import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/AtomicSourceBinding.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  WHERE THE ATOMIC PATH'S SOURCE BINDING COMES FROM.

  Both execution paths call the same validator:

      function _validateBundleDestinationContext(bytes32 bundleHash, InteropBundle memory b, uint256 proofChainId) {
          require(b.sourceChainId == proofChainId, WrongSourceChainId(...));         // (1)
          require(b.destinationChainId == block.chainid, WrongDestinationChainId(...));
          require(b.destinationBaseTokenAssetId == _expectedDestinationBaseTokenAssetId(), ...);
      }

  On the PUBLIC path `proofChainId` is the chain of the L1 message inclusion proof, so (1) is a genuine
  cross-check: a chain vouched for the message, and the bundle's declared origin must match it.

  On the ATOMIC path the argument is the bundle's own field:

      _validateBundleDestinationContext(bundleHash, interopBundle, interopBundle.sourceChainId);

  so (1) reads `x == x` and decides nothing.  The source comment says why, and is accurate:

      "An atomic bundle is never published to L1, so its source chain id is the bundle's own field; the
       cross-chain binding comes from the IMT inclusion proof (the atomicity gate) below."

  This file traces that binding to its end, because the field matters: `_executeCalls` passes
  `interopBundle.sourceChainId` into `sender: InteroperableAddress.formatEvmV1(_sourceChainId, from)` —
  the CALLER IDENTITY the recipient contract sees and authorises against.  A bundle that could lie
  about its source chain would be a cross-chain impersonation, so it is worth knowing exactly what
  stops it.

  The answer: the atomic path's source binding is EXACTLY the inclusion-self-binding argument of
  `ProofPolarity`, and therefore rests entirely on `HonestInsertion` (up to keccak collisions on
  named preimages).  Nothing else on that path constrains the field.  This file and its properties
  only state that answer; topic `AtomicSourceBindingStrong` derives it from the validator, the hash
  computation, the flow gate and the honest insertion of the one tree that vouched, and topic
  `SourceBindingReduced` from the vouching chain's whole source run.

  THREAT MODEL.  `_verifyBundle`'s comment states the premise plainly — "Asset correctness across
  chains is guaranteed by ZK proofs (assuming proofs are correct and CHAINS ARE NOT MALICIOUS)".  Under
  that premise this is sound and there is no defect here.  What this file adds is that the premise is
  load-bearing in a DIFFERENT place than the comment sits: it is written on the public path, which also
  has check (1) as an independent binding, while the atomic path — which has only the IMT argument —
  carries no such note.
-/

namespace AttackVectors.AtomicSourceBinding


variable {Chain Value Hash : Type*}


/-! The pieces, named after the deployed quantities:

* `declared h` — the `sourceChainId` field baked into bundle hash `h`.  Taking it as a function of
  `h` presupposes that `bundleHash = keccak(abi.encode(sourceChainId, bundleBytes))` determines the
  field: the encoding half is `BundleHashEncoding.abiEncode_inj`, but the hash half would be global
  keccak injectivity, which no map into `bytes32` has (topic `BundleHashPinned`).  Topic
  `AtomicSourceBindingStrong` uses the decoded field of the presented bytes instead, with keccak
  collisions on named preimages.
* `commit h` — `commitValue(flowId, h)`, the value the IMT proof is checked against.
* `tree c` — chain `c`'s authenticated IMT leaf set. -/

variable (declared : Hash → Chain) (commit : Hash → Value) (tree : Chain → Set Value)


/-- `HonestInsertion` transported to commit values: a chain's tree holds only commit values whose
bundle hash declares that chain.  It is meant as `ProofPolarity.HonestInsertion` composed with
`declared ∘ (commit⁻¹)`, and `LocalHonesty` as what reduces it to "every chain runs this code";
neither composition is proved here.  Quantified over every chain and hash, it is the conclusion of
`atomic_source_bound` itself.  The per-tree premise the code needs is
`AtomicSourceBindingStrong.TreeHoldsOwnLegs`, which a deployed center discharges
(`CenterRunTreeHoldsOwnLegs`). -/
def HonestCommits : Prop := ∀ (c : Chain) (h : Hash), commit h ∈ tree c → declared h = c


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
