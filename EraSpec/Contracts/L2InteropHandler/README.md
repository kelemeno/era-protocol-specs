# L2InteropHandler

## Headline guarantees

None yet at era-contracts `draft/v0.35.0` head `b17415d20`. The folder's current topic,
`AtomicSourceBinding`, is abstract and its main statement restates its premise; the derivations from
the handler's code were made for the old interop pin `c67894b9` and are kept under `History/`. A
model of `executeAtomicBundle` and `verifyAtomicBundle` at `b17415d20` is open work. Bundle replay
and self-call permission properties are under `../InteropHandlerBase/`.

## The current topic (`AtomicSourceBinding`)

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| AtomicSourceBinding | [Specs/AtomicSourceBinding.lean](Specs/AtomicSourceBinding.lean) | [Properties/AtomicSourceBinding.lean](Properties/AtomicSourceBinding.lean) | [Proofs/AtomicSourceBinding.lean](Proofs/AtomicSourceBinding.lean) |

At `b17415d20` both atomic entry points check the bundle's declared source chain against itself:
`executeAtomicBundle` (`interop/interop-handler/L2InteropHandler.sol:70`) and `verifyAtomicBundle`
(`:86`, through `_validateVerifiable`) pass `interopBundle.sourceChainId` as the proof chain to
`_validateBundleDestinationContext` (`InteropHandlerBase.sol:390-410`). The source comment
(`L2InteropHandler.sol:67-69`) says that source-chain authenticity comes from `requireFlowFinalized`
instead. The declared chain is what `_executeCalls` hands every recipient as the caller's chain
(`InteropHandlerBase.sol:378`).

The topic states this over three free symbols (`declared`, `commit`, `tree`): the binding holds when
each chain's tree holds only commit values of bundles that declare that chain (`HonestCommits`).
`atomic_source_bound` is that premise instantiated, so it derives nothing about the code;
`atomic_source_unbound_without_honest` shows the premise is not trivially true.
`Protocol/DestinationCapstone.lean` uses it.

## History

`History/` is a record of an older commit, not a claim about `b17415d20`. Three topics derived the
binding from the code of the old interop pin `c67894b9`. Three differences matter at `b17415d20`:

- the destination's bundle hash is `keccak256(_bundle)` (`InteropHandlerBase.sol:231`), where the
  pin hashed `abi.encode(interopBundle.sourceChainId, _bundle)`; the History models use the pin's
  preimage;
- `executeAtomicBundle` (`L2InteropHandler.sol:61-78`) accepts a `Verified` bundle and then skips
  `requireFlowFinalized`, and the new `verifyAtomicBundle` (`:83-92`) runs that gate and marks the
  bundle `Verified`; the History entry-point model has neither;
- the source side is the pin's `InteropCenter` `Dispatch` model.

| History topic (namespace) | What it derived at `c67894b9` | Files |
|---|---|---|
| SourceBindingReduced (`Contracts.SourceBinding.History`) | the binding from a run of the vouching chain's send-side code, up to the tree sentinel and keccak collisions on named preimages (`AtomicSourceBoundOrBreak`, `ExecutedBytesAreDispatchedOrBreak`, `ExecutedCallersAreSourceSendersOrBreak`; countermodel `WithoutOnlyInteropCenterSourceUnbound`) | [Specs](History/Specs/SourceBindingReduced.lean), [Properties](History/Properties/SourceBindingReduced.lean), [Proofs](History/Proofs/SourceBindingReduced.lean) |
| AtomicSourceBindingStrong (`AttackVectors.AtomicSourceBinding.History`) | the binding from the honest insertion of the one tree that vouched (`AtomicSourceBoundToVouchingTreeOrLoggedClash`, `CenterRunTreeHoldsOwnLegs`; countermodel `ForeignCommitInTreeUnbindsSource`) | [Specs](History/Specs/AtomicSourceBindingStrong.lean), [Properties](History/Properties/AtomicSourceBindingStrong.lean), [Proofs](History/Proofs/AtomicSourceBindingStrong.lean) |
| AtomicSourceBindingFaithful (`Contracts.L2InteropHandler.AtomicSourceFaithful.History`) | the binding over the pin's `executeAtomicBundle` itself: a successful execution locates its vouching leg and delivers every call with the declared source (`AtomicExecutionLocatesVouchingLeg`, `DeliveriesCarryDeclaredSource`, `AtomicSenderIsVouchingChainOrBreak`, `AtomicExecutionRunsTheDispatchedBundleOrBreak`; countermodel `MisbehavingLegChainImpersonates`) | [Specs](History/Specs/AtomicSourceBindingFaithful.lean), [Properties](History/Properties/AtomicSourceBindingFaithful.lean), [Proofs](History/Proofs/AtomicSourceBindingFaithful.lean) |

Their assumptions are `MODEL-SOURCE-BINDING` and `MODEL-ATOMIC-ENTRY` (ASSUMPTIONS.md). The insertion
authorization chain crosses contracts and is modelled in `../../Protocol/LocalHonesty.lean`.
