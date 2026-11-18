# NativeValueLegs

Source: era-contracts `draft/v0.35.0` at `b17415d20` (the same logic at `main` `70096e2ea`, up to
renames and line numbers; see the header of `Specs/LegConservation.lean`). Paths are relative to
`l1-contracts/contracts/`.

At the round-5 pin `c67894b9` an atomic call could not carry native `value`
(`InteropCenter._validateAtomicBundle`; `Contracts/InteropCenter` `Dispatch`, whose
`AtomicDispatchBurnsNothing` is a result about the pin). At head every L2→L2 send is atomic and a
direct call may carry `interopCallValue`. The sender pays it at send time
(`InteropCenter._ensureCorrectTotalValue`, `interop/InteropCenter.sol:418-460`): into
`BaseTokenHolder` when the destination has the same base token, otherwise burned or escrowed through
the router's handler for the destination's base-token asset (`AssetRouterBase.sol:97-116`). On
timeout, `AtomicFlowManager._recoverBundle` (`atomic-interop/AtomicFlowManager.sol:292-325`) refunds
each such call through `L2AssetRouter.bridgehubRecoverBaseToken` and the vault's
`bridgeRecoverFailedTransfer` (`bridge/asset-router/L2AssetRouter.sol:314-328`). This folder models
that round trip on the source chain and proves what a successful refund returns, to whom, in which
asset.

Namespace `Contracts.NativeValueLegs`. Statements are `Contracts.NativeValueLegs.Properties.*`; each
certificate has the same name without the `Properties` segment.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| LegConservation | [Specs/LegConservation.lean](Specs/LegConservation.lean) | [Properties/LegConservation.lean](Properties/LegConservation.lean) | [Proofs/LegConservation.lean](Proofs/LegConservation.lean) |
| LegConservationRuns | [Specs/LegConservationRuns.lean](Specs/LegConservationRuns.lean) | [Properties/LegConservationRuns.lean](Properties/LegConservationRuns.lean) | [Proofs/LegConservationRuns.lean](Proofs/LegConservationRuns.lean) |
| RouterRecoveryFrame | [Specs/RouterRecoveryFrame.lean](Specs/RouterRecoveryFrame.lean) | [Properties/RouterRecoveryFrame.lean](Properties/RouterRecoveryFrame.lean) | [Proofs/RouterRecoveryFrame.lean](Proofs/RouterRecoveryFrame.lean) |

## LegConservation: one collection, one refund

- **Bundle shape.** Under both indirect-starter checks (`IndirectCallOnlyToAssetRouter`,
  `IndirectCallCannotCarryValue`) and for a sender other than the router, every call sent from the
  router carries no value and `finalizeDeposit` data on an asset other than the destination's base
  token; every other call is the sender's; and the base-token refunds the loop requests are
  `(sender, v)` pairs summing to `totalBurnedCallsValue` (`ValueCallsComeFromTheSender`; witness
  `ValueCallsWitness`). The sender premise stands for an inventory fact (the router's code makes no
  call to the center), and it is load-bearing (`RouterSenderValueIsNotRefunded`). That inventory
  is argued from the source, not mechanised: no theorem enumerates the router's external calls.
- **The refund.** A successful `claimRefund` of such a bundle moves exactly `totalBurnedCallsValue`
  of the destination's base-token asset to the sender: out of the holder for the source chain's base
  token, out of the vault's escrow for a token native to the source chain (crediting the tracker's
  `chainBalance` by the same amount), or minted for a bridged token; the tracker's L1 counters do not
  move (`ClaimReturnsCollected`; witnesses `ClaimWitnessNativeToken`, `ClaimWitnessBaseToken`).
  Premises: the frame premise on router-call recovery and, if anything was collected, the asset
  registered in the tracker unless it is the base token.
- **The registration premise.** It is needed only for a token native to the source chain: a
  refund of a bridged token the tracker has not registered registers it and mints the same amount
  (`ClaimReturnsCollectedIfNativeRegistered`; witness `ClaimWitnessUnregisteredBridged`). For a
  native token it is load-bearing: the tracker's first registration sets the token's `chainBalance`
  to `MAX_TOKEN_BALANCE` minus the vault's holding (`L2AssetTracker.sol:246-251`) before the
  refund's credit (`UnregisteredNativeRefundSetsChainBalance`).
- **The collection.** Through the holder or the vault the send moves the same amount the other way
  (`CollectionTakesCollected`; witness `CollectionWitness`) and, when it collects anything, leaves
  the asset registered in the tracker (`CollectionRegistersAsset`; witness
  `CollectionRegistersWitness`), which discharges the refund's registration premise. The
  refund's change of the asset's footprint is the exact negation of the collection's
  (`RefundIsCollectionInverse`), and a refund right after the collection restores it
  (`RefundRestoresFootprint`; witness `RoundTripWitness`).
- **Countermodel.** Without `IndirectCallCannotCarryValue`, an indirect call's value is collected
  and nothing of it is refunded: its `from` is the router, so the loop sends it to
  `recoverAtomicCall` (`WithoutIndirectValueBanValueIsNotRefunded`).

## LegConservationRuns: refunds bound to sends along runs

A run interleaves atomic sends (collection included), `authorizeRefund` (one leg per step, proof
checks omitted), `claimRefund` on the bytes a claimant passes, and arbitrary other activity.

- **Headline.** Along every run from fresh manager storage, every successful claim consumed the leg
  of a logged send `s`; either it passed `s`'s own bytes, decoded `s`'s bundle and moved exactly
  `s`'s collected value to `s`'s sender in `s`'s asset, whenever `s` collected nothing, or collected
  through the holder or the vault, or the asset was registered in the tracker before the claim, or
  it does not originate on the source chain; or it passed other bytes with the same keccak, a
  collision on two named byte strings (`EveryClaimRefundsItsSenderOrCollision`; witness
  `RunClaimWitness`). Premises:
  `CodeFrames` (the abstract code frames other assets and clears no tracker registration), no logged
  send from the router, and the decoder round trip on the run's own bundles. No hash premise.
- **Once.** Each leg is committed by one send (`EachLegSentOnce`) and consumed by at most one claim
  (`EachLegClaimedAtMostOnce`); neither takes a premise.

## RouterRecoveryFrame: the frame premise through the vault

`L2AssetRouter.recoverAtomicCall` at head (`L2AssetRouter.sol:269-303`) with the vault's
`bridgeRecoverFailedTransfer` spelled out; only handlers other than the vault and the vault's deploy
branch stay abstract. The vault's refund of an asset other than `A` leaves `A`'s footprint and
registration alone, so the head recovery satisfies `RecoveryFramesOthers` whenever that remaining
code does (`HeadRouterRecoveryFramesOthers`), and `CodeFrames` when it also clears no registration
(`HeadCodeFrames`). The refund result then holds with the premise only on that code
(`ClaimReturnsCollectedHeadRouter`; witness `HeadRouterClaimWitness`, with a router-produced call
recovered through the vault).

## Model boundaries

One source chain. The vault's registry and `BASE_TOKEN_ASSET_ID` are configuration (write-once in
the source outside the upgrader's `updateL2`); the five contracts' `L1_CHAIN_ID` and the vault's and
tracker's `BASE_TOKEN_ASSET_ID` are one value each (`OPS-CONFIG`). Amounts are naturals; tokens are
standard ERC20s, and the supply-covers-balances invariant is a premise where a burn happens
(`SupplyCovers`). The collection is the value-moving component of the send; fees (backlog N-6) and
the indirect calls' own value are other components. The router's `recoverAtomicCall` and handlers
other than the vault are abstract code, constrained only by the stated frame premises
(`RecoveryFramesOthers`, `CodeFrames`). Reject-only checks are omitted (listed in the Specs header).
A call made by the refund recipient's code during a claim is a separate step. `abi.encode`/`abi.decode`
and keccak are abstract, with run-local premises only.

The refund results are about refunds that succeed; when a refund succeeds is not stated here. The
run headline leaves out one case: a claim that is the tracker's first registration of a token native
to the source chain. In the model that case needs a send that collected something through a handler
other than the vault (a send through the holder or the vault that collects anything registers its
asset, and registrations are never cleared). That a token in
the vault's registry is routed to the vault on the source router is argued from source and not
modelled: a registration on the source chain derives the asset id from its caller
(`AssetRouterBase.sol:65-77`) and the vault registers only itself
(`bridge/ntv/NativeTokenVaultBase.sol:492-499`), and the L1 vault accepts only the L2 vault as the
counterpart handler of its assets (`bridge/ntv/L1NativeTokenVault.sol:312-320`).

Not covered here: the destination side (backlog N-5 part 3). Full execution of a bundle at the
destination releases each call's `value` through `BaseTokenHolder.give`
(`interop/interop-handler/L2InteropHandler.sol:149-153` at head); the existing ledger result
`Contracts/InteropHandlerBase` `ValueLedgerFaithful` and the exclusion of "executed and refunded"
(`Protocol/InteropAtomicity`) are results about the pin `c67894b9` and are not restated at head.
