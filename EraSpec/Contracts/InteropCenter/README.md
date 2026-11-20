# InteropCenter

Target: era-contracts `draft/v0.35.0` head `b17415d20`, `l1-contracts/contracts/interop/InteropCenter.sol`
with `atomic-interop/AtomicFlowManager.sol` for the leg state that `append` writes.

## Headline guarantees

Every headline below is about one chain's center (and its flow manager) at `b17415d20`. Model
premises shared by all of them: one chain; the ABI encoder of `InteropBundle` and keccak are
abstract functions (`Params`), so no result assumes anything about them beyond its stated run-local
premise; checks that only reject and read nothing the model tracks are omitted, which only adds runs
(`MODEL-CENTER-HEAD`, `MODEL-FEE-STATE`, `MODEL-FEE-REENTRY` in `../../../ASSUMPTIONS.md`); upgrades
of the center or the manager are out of scope (`OPS-CONFIG`).

Send path (`Contracts.InteropCenter.Send.Properties.*`):

1. `SendMessageAlwaysAtomic`: a successful `sendMessage` step of the deployed code, from any state,
   carried `atomicBundle`, used that list's `parseAtomicSend`, sent to a chain other than L1, moved its
   leg from `Unset` to `Committed` and sent nothing to L1. No other premise.
2. `AtomicBundleAttributeMeansAppended`: for a successful step of the deployed code, from any state,
   through either entry point: with `atomicBundle`, the send is atomic, its bundle hash is one of the
   flow's legs declared from this chain, its leg moves from `Unset` to `Committed` (the IMT insert is
   not modelled) and nothing goes to L1; without it, the send goes to L1 and the manager is unchanged.
3. `EveryL2SendIsAtomic`: along any run of the deployed code from fresh storage, a dispatch was
   appended iff it was atomic iff its attribute list carries `atomicBundle`.
4. `PublishedMessagesAreWithdrawals`: along any run of the deployed code from fresh storage, every
   dispatch to L1 is a `sendBundle` without `atomicBundle` of one zero-value call from the asset
   router, with zero burned call value. The source-side value the router receives is not modelled.
5. `EachSaltDispatchesOnce`: along any run of the deployed code from fresh storage, the
   `(sender, salt)` keys of the dispatches are pairwise distinct. No hash premise.
6. `CommittedLegsAreCheckedDispatches`: along any run of the deployed code from fresh storage, every
   leg that is not `Unset` comes from a logged atomic dispatch of this chain with that flow id and
   bundle hash, accepted by `append`'s flow checks, whose value-carrying calls have the sender as
   `from` and whose other calls are zero-value calls from the asset router. No hash premise; the
   model includes direct `append` calls from other accounts.
7. `AtomicValueIsRefundedToPayer`: along any run of the deployed code from fresh storage, for a
   dispatch **whose sender is not the asset router**, the base-token refunds `_recoverBundle` would
   make go to the sender and add up to the burned call value. The payment itself is not modelled.
8. `ClaimedBundleIsDispatchedOrCollision`: along any run of the deployed code from fresh storage,
   **if the decoder inverts the encoder on the run's own bundles** (`SOL-ABI`), then for any bytes
   `x` whose leg `(f, keccak(x))` is not `Unset`, `x` is the encoding of a logged atomic dispatch of
   flow `f` and decodes to its bundle, or keccak collides on `x` and that encoding.
9. `EachLegAppendedOnce`: along any run from fresh storage, whatever the checks, the legs of the
   appended dispatches are pairwise distinct.
10. `DistinctDispatchesDistinctBundles`: along any run of the deployed code from fresh storage, two
    dispatches carry different bundles, or two different senders used the same salt and keccak
    collides on their packed preimages. No hash premise.
11. `AtomicBytesNeverPublished`: along any run from fresh storage, whatever the checks, **if the
    encoder separates the run's bundles**, no appended bundle's bytes are among the L1 messages.
12. `BundleHashCommittedUnderOneFlowOrClash`: along any run of the deployed code from fresh storage,
    **if the encoder separates the run's bundles**, two committed legs with one bundle hash have one
    flow id, or two logged dispatches clash (cross-sender salt clash or keccak collision on their
    encodings).

Fee state (`Contracts.InteropCenter.FeeState.Properties.*`, `…FeeState.Reentry.Properties.*`):

13. `ProtocolFeesBacked`: along any run from fresh storage of code **with the `msg.value`
    equalities** (the deployed code has them), the accrued protocol fees are at most the native
    balance.
14. `ZkFeesBacked`: **if the cached ZK token is a standard token** (`StandardTokens`), along any run
    from fresh storage the accrued ZK fees are zero while the token is unset and at most the
    center's balance of it.
15. `FeeUnitsAreL2Calls`: **with `onlyInteropCenter` on `append`** (deployed), along any run from any
    state the fee-unit counter grows by exactly the call count of the run's L2→L2 sends, which is
    the call count of the appended leaves.
16. `ProtocolFeeSetOnlyByBootloader`: every successful transaction leaves `interopProtocolFee`
    unchanged or is the bootloader's `setInteropFee`. No other premise.
17. `InitL2AtMostOnceAndFirst`: in every run from fresh storage, at most one `initL2`, and every
    send or claim comes after it. No other premise.
18. `OwnerHasNoFeePower`: the ownership entry points change only the owner fields, and every other
    transaction except `initL2` has the same outcome whoever the owner is. No other premise.
19. `NestedBackingNeverShrinks` (`FeeState.Reentry`): **with the `msg.value` equalities, and with
    `claimProtocolFees` writing before it pays (deployed) or holding the lock**, every successful
    call from any state, including every call nested in it, leaves the native balance minus the
    accrued protocol fees at least as large.

Witnesses: `Send.Properties.SendWitness`, `SendStepWitness`, `SendClaimWitness`,
`Properties.EncInjOnSatisfiable`, `Properties.KeccakInjOnSatisfiable` (`Common`);
`FeeState.Properties.FeeStateWitness`, `SendWitness`, `ClaimWitness`, `WriterWitness`,
`OwnershipWitness`; `FeeState.Reentry.Properties.NestedClaimInsideSendWitness`,
`PayFirstClaimLockNestedWitness`. Countermodels (`@[countermodel]`) show each check and each
disjunct is needed.

## Topics

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Common (vocabulary) | [Specs/Common.lean](Specs/Common.lean) | [Properties/Common.lean](Properties/Common.lean) | [Proofs/Common.lean](Proofs/Common.lean) |
| Send | [Specs/Send.lean](Specs/Send.lean) | [Properties/Send.lean](Properties/Send.lean) | [Proofs/Send.lean](Proofs/Send.lean) |
| FeeState | [Specs/FeeState.lean](Specs/FeeState.lean) | [Properties/FeeState.lean](Properties/FeeState.lean) | [Proofs/FeeState.lean](Proofs/FeeState.lean) |
| FeeReentry | [Specs/FeeReentry.lean](Specs/FeeReentry.lean) | [Properties/FeeReentry.lean](Properties/FeeReentry.lean) | [Proofs/FeeReentry.lean](Proofs/FeeReentry.lean) |

Statements are `…Properties.X`; each certificate has the same name without the `Properties` segment.

- **Send** (namespace `Contracts.InteropCenter.Send`): salts, the flow manager's legs, the ERC-7930
  attribute parser on decoded attributes, both entry points, the center's L1 messages, and
  `append`'s leg-membership and source-chain checks. Six checks are switches (`Checks`) so that
  countermodels can turn one off. A revert is the absence of a step; a send is one step
  (`nonReentrant`). `authorizeRefund` moves one leg per step without its proof checks, and
  `claimRefund` does not run `_recoverBundle`; `baseTokenRefunds` transcribes its base-token branch.
- **FeeState** (namespace `Contracts.InteropCenter.FeeState`) and its nested-call refinement
  **FeeReentry** (`…FeeState.Reentry`, `FlatIsNestedWithoutCalls`): balances, fee ledgers, fee
  parameters and the `INTEROP_FEE_UNITS_SLOT` counter, with every entry point, a direct `append`
  attempt and forced inflows.
- **Common**: the bundle and call structures, `FormsCall`, `saltPreimage`, `totalBurnedCallsValue`
  and the run-local premises `EncInjOn`/`KeccakInjOn`, shared by both models.

Send and FeeState model disjoint parts of the center's storage and share only the `Common`
vocabulary; they are not merged into one transition system.

## History

`History/` is the record of the old interop pin `c67894b9`, not a claim about `b17415d20`.

- `Dispatch`, `ClaimBinding`, `AtomicRouting` (namespace `Contracts.InteropCenter.History`): the send
  path at the pin, where `_validateAtomicBundle` rejected value-carrying atomic legs, the bundle hash
  was `keccak(abi.encode(chainid, abi.encode(bundle)))`, `append` took a flow id, and `sendMessage`
  always sent non-atomically. Other folders' pin models build on it (InteropHandlerBase
  `BundleStatusMachineStrong`, AtomicFlowManager `RecoveryLimitsFaithful`, Protocol
  `InteropAtomicity`, L2InteropHandler History).
- `SendMessageFinding` (namespace `Contracts.InteropCenter.Send.History`): the pin's parser accepted
  `atomicBundle` under `sendMessage`'s restriction while the pin's `sendMessage` sent non-atomically,
  so such a bundle was published to L1 instead of appended (`PinSendMessageDroppedAtomicBundle`).
  That was the round-5 source finding; at `b17415d20` every `sendMessage` is atomic
  (`SendMessageAlwaysAtomic`, `PinFindingRejectedAtHead`).
