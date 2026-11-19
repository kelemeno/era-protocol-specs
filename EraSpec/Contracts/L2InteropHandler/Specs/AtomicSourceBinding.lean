import Mathlib.Tactic


/-!
# Spec: where the atomic path's source binding comes from (abstract)

Source: era-contracts `draft/v0.35.0` head `b17415d20`, `l1-contracts/contracts/interop/interop-handler/`
(`IHB` is `InteropHandlerBase.sol`, `L2` is `L2InteropHandler.sol`).

Both handlers call the same validator (`IHB:390-410`):

    function _validateBundleDestinationContext(bytes32 bundleHash, InteropBundle memory b, uint256 proofChainId) {
        require(b.sourceChainId == proofChainId, WrongSourceChainId(...));            // (1)
        require(b.destinationChainId == block.chainid, WrongDestinationChainId(...));
        require(b.destinationBaseTokenAssetId == _getExpectedDestinationBaseTokenAssetId(), ...);
    }

On the L1 handler's path `proofChainId` is the chain of the L1 message inclusion proof
(`_validateVerifiable`, `IHB:306-314`, called with `_proof.chainId`), so (1) is a genuine
cross-check. On the L2 atomic path the argument is the bundle's own field, in `executeAtomicBundle`
(`L2:69`) and in `verifyAtomicBundle` (`L2:88`, through `_validateVerifiable`):

    _validateBundleDestinationContext(bundleHash, interopBundle, interopBundle.sourceChainId);

so (1) reads `x == x` and decides nothing. The source comment says why (`L2:66-68`): "`proofChainId`
is the bundle's own `sourceChainId` (self-binding), so the source-chain sub-check is a no-op;
source-chain authenticity is instead established by `requireFlowFinalized` below."

The field matters: `_executeCalls` passes it into
`sender: InteroperableAddress.formatEvmV1(_sourceChainId, interopCall.from)` (`IHB:378`), the caller
identity the recipient contract sees and authorises against. A bundle that could lie about its
source chain would be a cross-chain impersonation.

This topic states, over three free symbols, that the atomic path's source binding is exactly the
inclusion self-binding argument: it rests on each chain's tree holding only commit values of bundles
that declare that chain. It derives nothing from the code; its headline restates its premise. The
pin-era derivations from the code (`AtomicSourceBindingStrong`, `SourceBindingReduced`,
`AtomicSourceBindingFaithful`) are records of `c67894b9` under `History/`; at `b17415d20` the bundle
hash is `keccak256(_bundle)` (`IHB:231`), with no outer chain-id word.
-/

namespace AttackVectors.AtomicSourceBinding


variable {Chain Value Hash : Type*}


/-! The pieces, named after the deployed quantities:

* `declared h` — the `sourceChainId` field of the bundle whose hash is `h`.  Taking it as a function
  of `h` presupposes that `bundleHash = keccak(bundleBytes)` (`IHB:231`) determines the field: the
  bytes carry it at bytes 64..96 (`InteropDataEncoding` topic `BundleHashAtV35`), but the hash half
  would be global keccak injectivity, which no map into `bytes32` has (topic `BundleHashPinned`).  The
  History topic `AtomicSourceBindingStrong` (`c67894b9`) used the decoded field of the presented
  bytes instead, with keccak collisions on named preimages.
* `commit h` — `commitValue(flowId, h)`, the value the IMT proof is checked against.
* `tree c` — chain `c`'s authenticated IMT leaf set. -/

variable (declared : Hash → Chain) (commit : Hash → Value) (tree : Chain → Set Value)


/-- `HonestInsertion` transported to commit values: a chain's tree holds only commit values whose
bundle hash declares that chain.  It is meant as `ProofPolarity.HonestInsertion` composed with
`declared ∘ (commit⁻¹)`, and `LocalHonesty` as what reduces it to "every chain runs this code";
neither composition is proved here.  Quantified over every chain and hash, it is the conclusion of
`atomic_source_bound` itself.  The per-tree premise the code needs is
`History.TreeHoldsOwnLegs` (topic `AtomicSourceBindingStrong`, a record of `c67894b9`), which a
deployed center of that pin discharges (`History.Properties.CenterRunTreeHoldsOwnLegs`). -/
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
