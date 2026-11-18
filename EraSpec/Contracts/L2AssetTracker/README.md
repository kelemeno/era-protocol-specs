# L2AssetTracker

Source: `l1-contracts/contracts/bridge/asset-tracker/L2AssetTracker.sol` at era-contracts
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (`LaterHeads`: at `draft/v0.35.0` `b17415d20` and
`main` `70096e2ea`), with its callers in
`bridge/ntv/L2NativeTokenVault.sol`, `bridge/ntv/NativeTokenVaultBase.sol` and
`l2-system/BaseTokenHolder.sol`. The tracker keeps, per asset, a chain balance for tokens native
to this chain, a pre-v31 total-supply snapshot taken at registration, and two counters of flows
to and from L1 while the chain settles on L1.

Topic `RecoveryNeutrality` is pinned to `draft/v0.35.0` head
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5` instead, with the paths of the native token vault, the
base-token holder, the L2 asset router, the atomic flow manager and the interop center that reach
it; `main` at `70096e2ea6eeb5373992e178064c4b26dcf6436a` has the same code on these paths.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Accounting: storage, the nine entry points, runs, the chain-balance invariant | [Specs/Accounting.lean](Specs/Accounting.lean) | [Properties/Accounting.lean](Properties/Accounting.lean) | [Proofs/Accounting.lean](Proofs/Accounting.lean) |
| HookOrdering: the tracker hook before the token effect on the vault's four paths | [Specs/HookOrdering.lean](Specs/HookOrdering.lean) | [Properties/HookOrdering.lean](Properties/HookOrdering.lean) | [Proofs/HookOrdering.lean](Proofs/HookOrdering.lean) |
| NativeEscrow: runs of the tracker together with a native token's ledger | [Specs/NativeEscrow.lean](Specs/NativeEscrow.lean) | [Properties/NativeEscrow.lean](Properties/NativeEscrow.lean) | [Proofs/NativeEscrow.lean](Proofs/NativeEscrow.lean) |
| LaterHeads: the tracker at `b17415d20`/`70096e2ea` and the recovery guard they add | [Specs/LaterHeads.lean](Specs/LaterHeads.lean) | [Properties/LaterHeads.lean](Properties/LaterHeads.lean) | [Proofs/LaterHeads.lean](Proofs/LaterHeads.lean) |
| RecoveryNeutrality | [Specs/RecoveryNeutrality.lean](Specs/RecoveryNeutrality.lean) | [Properties/RecoveryNeutrality.lean](Properties/RecoveryNeutrality.lean) | [Proofs/RecoveryNeutrality.lean](Proofs/RecoveryNeutrality.lean) |

The vault's side of the hooks (the L1 vault's `bridgedOut` ledger and the L2 vault's calls into
this tracker, as hooks of the vault model) is the `TrackerHooks` topic of
[NativeTokenVaultBase](../NativeTokenVaultBase/README.md).

Namespace `Contracts.L2AssetTracker`. Statements are `Contracts.L2AssetTracker.Properties.*`;
each certificate has the same name without the `Properties` segment.

- **What the chain balance of a native token is.** Along every run from a state satisfying
  `Inv` (fresh storage satisfies it, `FreshTrackerSatisfiesInv`), for a registered asset native
  here, `chainBalance + Σout = snapshot + Σin`, so `chainBalance = MAX - (E + Σout - Σin)` with
  `E = MAX - snapshot`: `0` for a token registered as new, the vault's balance as the first touch
  read it for a legacy one (`NativeSentinel`; invariant `AccountingInvariant`). `Σout` and `Σin`
  are a ghost audit of the successful flow calls (by the vault, the base-token holder and the L2
  base token).
- **The cap.** For such an asset, an inbound transfer touching no L1 counter succeeds iff
  `Σin + amount ≤ E + Σout` (`InflowOverflowIsCap`); an outbound one, for an asset whose
  `tokenAddress` the vault has set, iff `E + Σout + amount ≤ MAX + Σin` (`OutflowIffNetOutFits`).
  `ChainBalanceGatesInflow` is a run, after `initL2`, in which the same inbound transfer reverts
  before an outbound one and succeeds after it.
- **The escrow behind it.** Run together with the token's ledger (the vault's two native paths,
  first touches reading the token as it is, every other tracker call, and every ledger change the
  vault does not make), `E + Σout - Σin` is at most the vault's balance of the token
  (`NativeReleasesAreEscrowed`). So, with a nonzero vault address, for a registered asset an
  inbound native transfer to a nonzero receiver, touching no L1 counter, succeeds exactly within
  the cap (`NativeInboundIffCap`); in general it fails only where the tracker's hook does
  (`NativeInboundFailsOnlyAtTheHook`); and, with a nonzero chain id and `tokenAddress` entry, a
  nonzero depositor other than the vault holding `amount` can always move it out on the outbound
  native path, first touch included, unless `totalWithdrawalsToL1` would overflow
  (`FundedNativeOutboundSucceeds`; allowances are not modelled). The model's one assumption about
  the ledger, that nothing but the vault's withdrawal lowers the vault's balance, is needed
  (`EscrowNeedsVaultOnlyOutflow`).
- **Round trips.** An outbound call followed by an inbound one of the same chain, asset and
  amount restores the storage up to the first-touch registration, when the other chain is not L1
  or this chain settles off L1 at both calls (`TrackerHooksCancelOffL1`); with L1 while settling
  on L1, unless the deposit counter would overflow, both L1 counters rise by the amount
  (`L1CountersMoveTogether`).
- **First-touch snapshots.** The vault calls the hook before it burns, deposits, mints or
  withdraws, so a first touch records the token as it was before the call, whichever path makes
  it (`FirstTouchSnapshotIsPreOp`, `SnapshotIndependentOfEntry`); the vault model's preparation,
  mint and recovery with the L2 hooks, the vault calling the tracker, give what the bridged paths
  give (`HookPrecedesEffect`). In the reversed order, which no source path runs, the outbound and
  inbound paths can record different snapshots, neither the pre-call one
  (`HookAfterEffectSkews`). Once registered, the tracker does not read the token
  (`TokenReadsIgnoredOnceRegistered`), and once `initL2` has run with the base token registered,
  the base token's first touch is the identity (`BaseNeverTakesLegacyPath`).
- **The base token and registration.** Once the base token is registered, the inbound base path
  never changes a chain balance (`BaseFinalizeNeverCreditsChainBalance`), while the outbound one
  debits a base token native to this chain; with such a base token a round trip breaks the
  sentinel (`BaseTokenNativeAsymmetry`), which is why `Inv` has the premise `BaseNotSelfNative`.
  Registration is monotone and the snapshot is written once, except by the backfill
  (`RegistrationMonotone`), which writes only the base token's snapshot from a saved zero
  (`BackfillOnlyBaseFromZero`) and, on a run from a state satisfying `Inv`, happens at most once
  (`BackfillAtMostOnce`).

Witnesses: `AccountingRunSatisfiable`, `TrackerRoundTripSatisfiable`, `BaseFinalizeSatisfiable`,
`BackfillSatisfiable`, `FirstTouchSatisfiable`, `HookPrecedesEffectSatisfiable`,
`BaseNeverLegacySatisfiable`, `NativeEscrowSatisfiable` (a composed run from a fresh tracker
through `initL2`, with a nonzero vault balance before registration, a direct transfer into the
vault after it, and nonzero flows both ways). The runs and storages of the witnesses are reached
from fresh storage through `initL2`. The countermodels are their own witnesses. No result takes a
hash premise.

Model boundaries (`MODEL-L2-TRACKER` in the [assumption register](../../../ASSUMPTIONS.md)):
`block.chainid`, the system addresses and the vault's `originChainId`/`tokenAddress` entries are
a fixed `Config`; the settlement layer is changed by a step of its own. A revert is the absence of
a step. The token reads of a first touch are free inputs in `Accounting`; `HookOrdering` computes
them from the token model's ledger for one call, and `NativeEscrow` composes the ledger with whole
runs, for one asset. A native token is modelled by the token model's ledger, without allowances.
Not modelled: the inherited ownership and pause slots, events, `L2NativeTokenVault.updateL2`
rewriting the base token's vault entries, upgrades (`OPS-CONFIG`), the value movement of the base
token through `BaseTokenHolder`, and the vault's own other checks around a hook (router, pause,
amount, asset id, WETH, `msg.value`, and `_withdrawFunds`' base-asset check). Fresh storage is the
starting point of a newly deployed tracker only.

## Later heads

At `draft/v0.35.0` `b17415d20` and `main` `70096e2ea` the tracker is the same code (the files
differ in two comments; the first is also the file at the upgrade pin `e561b9cc2`). Against the
pin, the backfill, `registerBaseTokenDuringUpgrade` and `initL2`'s backfill flag are gone, and the
new view `assertRecoveryIsAccountingNeutral` reverts a recovery whose original destination is L1,
and one of the tracker's base asset when it is native to this chain; the L2 vault calls it before
any refund. The registration and flow functions and their callers' arguments are unchanged.
`LaterHeads` models those heads:

- **The accounting results carry over.** From a state whose backfill flag is clear while
  `initL2` has not run, a run at the heads is a run of the pin model (`HeadRunIsPinRun`), so
  `HeadAccountingInvariant`, `HeadNativeSentinel`, `HeadInflowOverflowIsCap`,
  `HeadOutflowIffNetOutFits` and `HeadBaseNeverTakesLegacyPath` hold there.
- **So do the escrow results.** A composed run with a native token at the heads
  (`HeadEscrowStep`) is a composed run of `NativeEscrow` (`HeadEscrowRunIsEscrowRun`), so
  `HeadEscrowInvariant`, `HeadNativeReleasesAreEscrowed`, `HeadNativeInboundIffCap` and
  `HeadFundedNativeOutboundSucceeds` hold there. `HookOrdering`'s single-call statements are about
  the flow functions and the vault's paths, which are the pin's code at the heads; its recovery
  conjunct is the pin's recovery, which the heads run when the guard holds.
- **The guard closes the L1-counter gaps.** With the L2 hooks, after a successful preparation on
  a `WellFormed` vault state, the heads' recovery of the returned data, applied to the prepared
  state with only the settlement layer changed (to any layer), succeeds exactly when the guard
  holds and then restores the vault state and the tracker storage up to the first-touch
  registration (`HeadRecoveryRestoresVaultAndTracker`). The pin's divergent recovery to L1 reverts
  there (`HeadGuardRejectsPinDivergence`). The router's own checks at the heads
  (`L2AssetRouter.recoverAtomicCall`, which also rejects an L1 destination: `L2AssetRouter.sol:275`
  at `b17415d20`, `:281` at `70096e2ea`) are not modelled.

Witnesses: `HeadRunSatisfiable` (a run through the heads' `initL2` with a legacy native asset and
flows both ways), `HeadBaseNeverLegacySatisfiable` (the heads' `initL2`, the vault's registration of
the base asset, and base-token flows both ways), `HeadNativeEscrowSatisfiable` (the composed run of
`NativeEscrowSatisfiable` through the heads' `initL2`), `HeadRecoverySatisfiable` (an unregistered
asset, a settlement-layer change before the recovery, and a successful recovery).

## RecoveryNeutrality: atomic recovery on the tracker at v35

The model (namespace `Contracts.L2AssetTracker.RecoveryNeutrality`) keeps the tracker's live storage
(`chainBalance`, `isAssetRegistered`, `interopInfo`, `totalPreV31TotalSupply`), the vault's
`originChainId`/`tokenAddress`, the router's `assetHandlerAddress`, the base-token holder's balance,
the settlement layer, and a ghost log of bridge-outs and recoveries. Its operations are every write to
that state at v35: registrations, the vault's `bridgeBurn`/`bridgeMint`, the interop center's
same-base-token value burn, the holder's `give`, the runtime's base-token hook, migrations, handler
writes, and `claimRefund` through `recoverAtomicCall`/`bridgehubRecoverBaseToken` down to the vault's
`bridgeRecoverFailedTransfer` and the holder's `recoverBaseToken`. Each of the recovery path's checks
can be switched off (`Guards`) for the countermodels; `Guards.v35` is the source.

- **L1 destinations.** At v35 every recovery entry point rejects an L1 destination
  (`RecoveryToL1RevertsAtV35`). Each of the four L1 checks (flow manager, router, the vault's and the
  holder's calls of the tracker check) rejects every recovery that reaches it on its own
  (`EachL1CheckSufficesOnItsPath`, `L1RecoveryRejectionWitness`). With every recovery check removed
  (`Guards.none`; the two base-origin checks are off this path), a run
  that bridges out toward L1 while settling on L1 and then claims a bundle toward L1 recovering the
  same amount succeeds: `totalWithdrawalsToL1` still counts the bridge-out and the recovery is also
  counted in `totalSuccessfulDepositsFromL1` (`L1ChecksLoadBearing`). The model lets a claim name any
  bundle; in the source the interop center never appends a bundle toward L1 (`IC:552-553`,
  `:733-742`), a further check outside the model, so this countermodel is about the recovery-side
  checks alone.
- **Round trip.** A bridge-out of `x` of `a` toward `d`, any run of steps not on `a`, and recoveries
  of `a` totalling `x`: `a`'s tracker entries end as its first-touch registration left them, and the
  holder's balance is restored for the base asset (`BurnThenRecoveriesRestoreAsset`,
  `InteropValueBurnThenRecoveriesRestoreBase`). The recoveries succeed when the destination is not L1
  and the base asset is not recorded as native here (`RecoveriesAfterBurnSucceed`), and a claim is
  exactly those vault recoveries (`ClaimRefundIsVaultRecoveries`, `BurnThenClaimRestores`). Other
  steps may also fall between the recoveries (`BurnThenInterleavedRecoveriesRestoreAsset`).
- **Balanced flows.** For an asset the tracker has registered and the vault has a token for (with the
  vault as its handler when a router call names it, and for the base asset a non-native origin): in
  a nested run, where other steps and other claims' calls may fall between the calls of a claim,
  whose steps on the asset are bridge-outs toward chains other than L1 and calls of claims, with
  equal bridged-out and recovered totals, the asset's view ends as it started, in any order and with
  any number of bridge-outs and claims (`BalancedFlowsRestoreAsset`, `BalancedFlowsWitness`).
- **One recovery.** It never writes `interopInfo`; for an asset other than the base asset it adds
  exactly the amount to `chainBalance[block.chainid][a]` if native here; for the base asset it writes
  no tracker entry and needs the base asset to be recorded as not native here
  (`VaultRecoveryEffectAtV35`, `ClaimRefundNeverWritesInteropInfo`).
- **Ledger.** `totalWithdrawalsToL1[a]` grows by exactly the logged bridge-outs of `a` toward L1 made
  while settling on L1, under any checks; with the flow manager's check no recovery has an L1
  destination (`WithdrawalsToL1Ledger`). The same holds for nested runs, and every run is one
  (`WithdrawalsToL1LedgerNested`, `NestedLedgerWitness`). That a counted L1 bridge-out is never
  refunded through a claim toward another chain depends on the claim naming its own appended
  bundle, which is not modelled.
- **Boundary.** A native re-credit succeeds exactly when it fits in a word (`RecoveryCreditFitsIff`):
  an inbound transfer between a bridge-out and its claim can make the whole claim revert
  (`InflowBeforeRecoveryBlocksClaim`). Without the base-token origin checks, a base token recorded as
  native here (which the source's comments say does not occur) is refunded from the holder while its
  chain balance stays lowered (`BaseOriginCheckLoadBearing`).

Model boundary: `MODEL-RECOVERY-NEUTRALITY` in `../../../ASSUMPTIONS.md`. Token contracts, the release
of funds and its possible revert, code reached through foreign handlers, the leg state of
`claimRefund` and which bundles were sent are not modelled (a claim may name any bundle); the router's
burn-side handler dispatch is not modelled (bridge-outs are taken at the vault); the copies of
`L1_CHAIN_ID` and `BASE_TOKEN_ASSET_ID` are one value each. This topic's model is self-contained: it
does not reuse another topic's tracker model. This folder does not certify the compiled contracts.
