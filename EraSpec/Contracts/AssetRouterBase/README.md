# AssetRouterBase

Source: `contracts/bridge/asset-router/AssetRouterBase.sol` in the pinned
era-contracts tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), function
`_setAssetHandlerAddressThisChain`, the only writer of `assetHandlerAddress` and
`assetDeploymentTracker`. `L1AssetRouter` and `L2AssetRouter` reach it through
`setAssetHandlerAddressThisChain`; the model starts at the internal function.
The model's header quotes the function body, and that quotation matches the
pinned source.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| HandlerRegistration | [Specs/HandlerRegistration.lean](Specs/HandlerRegistration.lean) | [Properties/HandlerRegistration.lean](Properties/HandlerRegistration.lean) | [Proofs/HandlerRegistration.lean](Proofs/HandlerRegistration.lean) |

Namespace: `Contracts.AssetRouter`. Statements are `Contracts.AssetRouter.Properties.*`;
each certificate has the same name without the `Properties` segment.

## Assumptions to review

`NoHijack` and `NtvTouchesOnlyItsOwnIds` take `IdAssumptions enc` as a premise.
Its `inj` field states that `encodeAssetId` is injective on all
(chain, sender, data) triples of 256-bit words. No function into 256-bit words
can satisfy that, so as stated those two properties hold vacuously. See
`CRYPTO-ID` in the [assumption register](../../../ASSUMPTIONS.md). The other six
properties do not use the premise. Restating the two with a bounded or
reduction-style premise is open.

Everything here is abstract. Events, `_setAssetHandler`'s other effects, the
L1-to-L2 counterpart registration path, and ABI encoding of the id preimage are
not modelled.
