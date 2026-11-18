# L2AssetTracker

Source: `l1-contracts/contracts/bridge/asset-tracker/L2AssetTracker.sol` at era-contracts
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (`LaterHeads`: at `draft/v0.35.0` `b17415d20` and
`main` `70096e2ea`), with its callers in
`bridge/ntv/L2NativeTokenVault.sol`, `bridge/ntv/NativeTokenVaultBase.sol` and
`l2-system/BaseTokenHolder.sol`. The tracker keeps, per asset, a chain balance for tokens native
to this chain, a pre-v31 total-supply snapshot taken at registration, and two counters of flows
to and from L1 while the chain settles on L1.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Accounting: storage, the nine entry points, runs, the chain-balance invariant | [Specs/Accounting.lean](Specs/Accounting.lean) | [Properties/Accounting.lean](Properties/Accounting.lean) | [Proofs/Accounting.lean](Proofs/Accounting.lean) |
| HookOrdering: the tracker hook before the token effect on the vault's four paths | [Specs/HookOrdering.lean](Specs/HookOrdering.lean) | [Properties/HookOrdering.lean](Properties/HookOrdering.lean) | [Proofs/HookOrdering.lean](Proofs/HookOrdering.lean) |
| NativeEscrow: runs of the tracker together with a native token's ledger | [Specs/NativeEscrow.lean](Specs/NativeEscrow.lean) | [Properties/NativeEscrow.lean](Properties/NativeEscrow.lean) | [Proofs/NativeEscrow.lean](Proofs/NativeEscrow.lean) |
| LaterHeads: the tracker at `b17415d20`/`70096e2ea` and the recovery guard they add | [Specs/LaterHeads.lean](Specs/LaterHeads.lean) | [Properties/LaterHeads.lean](Properties/LaterHeads.lean) | [Proofs/LaterHeads.lean](Proofs/LaterHeads.lean) |

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
