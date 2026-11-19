# L2AssetTracker

## Headline guarantees

About era-contracts `draft/v0.35.0` head `b17415d20`. Names are under `Contracts.L2AssetTracker`;
each statement is `….Properties.<Name>` and its proof `….<Name>`. "A run" is any sequence of
successful tracker calls at `b17415d20` (`HeadReach`: every entry point by its permitted caller,
with any arguments and token reads, and any change of settlement layer).

- `HeadAccountingInvariant`: along every run from a state satisfying `Inv`, `Inv` keeps holding.
  Premise: the start satisfies `Inv`: an unregistered asset has no recorded flows and no chain
  balance here, a registered asset native here satisfies the sentinel below with its snapshot
  saved, and the base token is not native to this chain. Fresh storage satisfies it when neither
  the base asset `initL2` installs nor asset id `0` is native here (`FreshTrackerSatisfiesInv`).
- `HeadNativeSentinel`: after such a run, for a registered asset native here,
  `chainBalance + Σout = snapshot + Σin`, where `Σout`, `Σin` are the amounts of the successful
  outbound and inbound flow calls. Same premise.
- `HeadNativeReleasesAreEscrowed`: run together with the token's ledger (the vault's two native
  paths, every other tracker call, and any ledger change the vault does not make), what the
  tracker still lets in for a registered native asset is at most the vault's balance of the token.
  Premises: the start satisfies `Inv`, the ledger is well formed (balances sum to the supply, the
  supply is below `2^256`), the escrow bound holds at the start once registered, and nothing but
  the vault's own withdrawal lowers the vault's balance (`EscrowNeedsVaultOnlyOutflow` shows this
  last premise is needed).
- `HeadNativeInboundIffCap`: in that composed run, an inbound native transfer of a registered asset
  succeeds exactly when `Σin + amount ≤ E + Σout` (`E = MAX - snapshot`). Premises: as above, plus
  a nonzero vault address and receiver, and the other chain is not L1 or this chain does not
  settle on L1.
- `HeadFundedNativeOutboundSucceeds`: in that composed run, a depositor holding `amount` can move it
  out on the native outbound path. Premises: as above, plus nonzero chain id, vault address and
  token address, a nonzero depositor other than the vault, and, toward L1 while settling on L1, no
  overflow of `totalWithdrawalsToL1`. Allowances are not modelled.
- `HeadRecoveryRestoresVaultAndTracker`: after a successful preparation on a well-formed vault
  state, the guarded recovery of the returned data (with the settlement layer changed to any value
  in between) succeeds exactly when `assertRecoveryIsAccountingNeutral` holds, and then restores the
  vault state and the tracker storage up to the first-touch registration. Premise: the vault model's
  well-formedness (`WellFormed`).
- `RecoveryNeutrality.RecoveryToL1RevertsAtV35`: every recovery entry point (`claimRefund`,
  `recoverAtomicCall`, `bridgehubRecoverBaseToken`, the vault's `bridgeRecoverFailedTransfer`, the
  holder's `recoverBaseToken` of a nonzero amount) reverts for an L1 destination. No premise.
- `RecoveryNeutrality.BurnThenRecoveriesRestoreAsset`: a vault bridge-out of `x` of `a` toward `d`,
  then any steps not on `a`, then vault recoveries of `a` toward `d` totalling `x`, leave `a`'s
  tracker entries as its first-touch registration left them, its registry and handler entries as
  they were, and the holder's balance as it was for the base asset. Premise: those three run
  segments succeed.
- `RecoveryNeutrality.ClaimRefundNeverWritesInteropInfo`: a successful `claimRefund` writes no
  `interopInfo`, lowers no chain balance, and does not raise the holder's balance. No premise.
- `RecoveryNeutrality.WithdrawalsToL1Ledger`: along any run, `totalWithdrawalsToL1[a]` grows by
  exactly the logged bridge-outs of `a` toward L1 made while settling on L1; with the flow
  manager's check, no recovery has an L1 destination. No premise.

`RecoveryNeutralityRefinement` shows that the tracker inside `RecoveryNeutrality` is this folder's
canonical tracker model, so all of the above are about one tracker.

## Topics

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Accounting: storage, the entry points, runs, the chain-balance invariant | [Specs/Accounting.lean](Specs/Accounting.lean) | [Properties/Accounting.lean](Properties/Accounting.lean) | [Proofs/Accounting.lean](Proofs/Accounting.lean) |
| HookOrdering: the tracker hook before the token effect on the vault's four paths | [Specs/HookOrdering.lean](Specs/HookOrdering.lean) | [Properties/HookOrdering.lean](Properties/HookOrdering.lean) | [Proofs/HookOrdering.lean](Proofs/HookOrdering.lean) |
| NativeEscrow: runs of the tracker together with a native token's ledger | [Specs/NativeEscrow.lean](Specs/NativeEscrow.lean) | [Properties/NativeEscrow.lean](Properties/NativeEscrow.lean) | [Proofs/NativeEscrow.lean](Proofs/NativeEscrow.lean) |
| LaterHeads: the `b17415d20` step and the recovery guard | [Specs/LaterHeads.lean](Specs/LaterHeads.lean) | [Properties/LaterHeads.lean](Properties/LaterHeads.lean) | [Proofs/LaterHeads.lean](Proofs/LaterHeads.lean) |
| RecoveryNeutrality: atomic recovery on the tracker, with the vault, router, holder and flow manager | [Specs/RecoveryNeutrality.lean](Specs/RecoveryNeutrality.lean) | [Properties/RecoveryNeutrality.lean](Properties/RecoveryNeutrality.lean) | [Proofs/RecoveryNeutrality.lean](Proofs/RecoveryNeutrality.lean) |
| RecoveryNeutralityRefinement: `RecoveryNeutrality`'s tracker is the canonical one | [Specs/RecoveryNeutralityRefinement.lean](Specs/RecoveryNeutralityRefinement.lean) | [Properties/RecoveryNeutralityRefinement.lean](Properties/RecoveryNeutralityRefinement.lean) | [Proofs/RecoveryNeutralityRefinement.lean](Proofs/RecoveryNeutralityRefinement.lean) |
| History: the pin's base-token backfill | — | [History/Properties/Backfill.lean](History/Properties/Backfill.lean) | [History/Proofs/Backfill.lean](History/Proofs/Backfill.lean) |

## The model

The canonical model is `Specs/Accounting.lean`: the tracker's storage (`chainBalance`,
`isAssetRegistered`, `interopInfo`, `totalPreV31TotalSupply`, `L1_CHAIN_ID`, `BASE_TOKEN_ASSET_ID`,
the reentrancy-guard slot), its entry points with their permitted callers and the arguments the
vault, the base-token holder, the L2 base token and the upgrader pass, and a ghost audit of flow
amounts. `Step` also has three operations that exist only at the pin `c67894b9` (the base-token
backfill, `registerBaseTokenDuringUpgrade`, `initL2`'s backfill flag); the `b17415d20` step is
`HeadStep` (`Specs/LaterHeads.lean`), and every `HeadStep` run is a `Step` run (`HeadRunIsPinRun`).
So the `Step`-run results of `Accounting`, `HookOrdering` and `NativeEscrow` (the cap
`InflowOverflowIsCap`, `OutflowIffNetOutFits`, the round trips `TrackerHooksCancelOffL1` and
`L1CountersMoveTogether`, the first-touch results `FirstTouchSnapshotIsPreOp`,
`SnapshotIndependentOfEntry`, `HookPrecedesEffect`, `TokenReadsIgnoredOnceRegistered`,
`BaseNeverTakesLegacyPath`, `BaseFinalizeNeverCreditsChainBalance`, `RegistrationMonotone`) cover
every run at `b17415d20`; `LaterHeads` restates the main ones over `HeadReach` directly.

Witnesses and countermodels: `AccountingRunSatisfiable`, `TrackerRoundTripSatisfiable`,
`BaseFinalizeSatisfiable`, `FirstTouchSatisfiable`, `HookPrecedesEffectSatisfiable`,
`BaseNeverLegacySatisfiable`, `NativeEscrowSatisfiable`, `HeadRunSatisfiable`,
`HeadBaseNeverLegacySatisfiable`, `HeadNativeEscrowSatisfiable`, `HeadRecoverySatisfiable`;
`ChainBalanceGatesInflow`, `BaseTokenNativeAsymmetry` (why `Inv` assumes the base token is not
native here), `HookAfterEffectSkews` (the reversed hook order, which no source path runs),
`EscrowNeedsVaultOnlyOutflow`, `HeadGuardRejectsPinDivergence`. No result takes a hash premise.

`RecoveryNeutrality` is a second, richer model of the same code: the tracker's storage, the vault's
`originChainId`/`tokenAddress`, the router's handlers, the base-token holder's balance, the
settlement layer and a ghost log, with every write to that state at `b17415d20` as a step,
including `claimRefund` down to the vault's and the holder's recoveries. `Guards` switches each
recovery check for the countermodels (`L1ChecksLoadBearing`, `BaseOriginCheckLoadBearing`);
`Guards.v35` is the source. `RecoveryNeutralityRefinement` proves that its four flow hooks and two
registrations, mapped through the storage projection `toStorage`, are the canonical entry points,
and that its vault recovery checks are the canonical `RecoveryAccountingNeutral`.

Model boundaries: `MODEL-L2-TRACKER` and `MODEL-RECOVERY-NEUTRALITY` in the
[assumption register](../../../ASSUMPTIONS.md). `block.chainid`, the system addresses and the vault's
entries are fixed configuration in `Accounting`; the token reads of a first touch are free inputs
except in `HookOrdering` and `NativeEscrow`, which read them from the token model's ledger. The
router's own checks in front of a recovery, token contracts, and the release of funds are not
modelled. This folder does not certify the compiled contracts.

## History

`History/` is the record of the pin `c67894b9`, not a claim about `b17415d20`:
`History.BackfillOnlyBaseFromZero`, `History.BackfillAtMostOnce` and `History.BackfillSatisfiable`
are about the base-token backfill, which `b17415d20` removed.
