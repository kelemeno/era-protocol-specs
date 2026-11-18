# L2AssetTracker

Source: `contracts/bridge/asset-tracker/L2AssetTracker.sol` at era-contracts `draft/v0.35.0` head
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, with the paths of the native token vault, the base-token
holder, the L2 asset router, the atomic flow manager and the interop center that reach it. `main` at
`70096e2ea6eeb5373992e178064c4b26dcf6436a` has the same code on these paths.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| RecoveryNeutrality | [Specs/RecoveryNeutrality.lean](Specs/RecoveryNeutrality.lean) | [Properties/RecoveryNeutrality.lean](Properties/RecoveryNeutrality.lean) | [Proofs/RecoveryNeutrality.lean](Proofs/RecoveryNeutrality.lean) |

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
  (`EachL1CheckSufficesOnItsPath`, `L1RecoveryRejectionWitness`). With the four checks removed, a run
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
  (`WithdrawalsToL1LedgerNested`, `NestedLedgerWitness`).
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
