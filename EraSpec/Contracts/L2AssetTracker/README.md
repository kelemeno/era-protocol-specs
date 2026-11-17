# L2AssetTracker

Source: `l1-contracts/contracts/bridge/asset-tracker/L2AssetTracker.sol` at era-contracts
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`, with its callers in
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
  are a ghost audit of the vault's and the base-token holder's successful flow calls.
- **The cap.** For such an asset, an inbound transfer touching no L1 counter succeeds iff
  `Σin + amount ≤ E + Σout` (`InflowOverflowIsCap`); an outbound one iff
  `E + Σout + amount ≤ MAX + Σin` (`OutflowIffNetOutFits`). `ChainBalanceGatesInflow` is a run in
  which the same inbound transfer reverts before an outbound one and succeeds after it.
- **The escrow behind it.** Run together with the token's ledger (the vault's two native paths,
  first touches reading the token as it is, every other tracker call, and every ledger change the
  vault does not make), `E + Σout - Σin` is at most the vault's balance of the token
  (`NativeReleasesAreEscrowed`). So an inbound native transfer to a nonzero receiver succeeds
  exactly within the cap (`NativeInboundIffCap`) and fails only where the tracker's hook does
  (`NativeInboundFailsOnlyAtTheHook`), and a depositor other than the vault holding `amount` can
  always move it out on the outbound native path, first touch included, unless
  `totalWithdrawalsToL1` would overflow (`FundedNativeOutboundSucceeds`). The model's one assumption about the ledger, that nothing but
  the vault's withdrawal lowers the vault's balance, is needed (`EscrowNeedsVaultOnlyOutflow`).
- **Round trips.** An outbound call followed by an inbound one of the same chain, asset and
  amount restores the storage up to the first-touch registration, when the chain is not L1 or the
  chain settles off L1 at both calls (`TrackerHooksCancelOffL1`); to L1 while settling on L1 both
  L1 counters rise by the amount (`L1CountersMoveTogether`).
- **First-touch snapshots.** The vault calls the hook before it burns, deposits, mints or
  withdraws, so a first touch records the token as it was before the call, whichever path makes
  it (`FirstTouchSnapshotIsPreOp`, `SnapshotIndependentOfEntry`); the vault model's preparation,
  mint and recovery with the L2 hooks give what the bridged paths give (`HookPrecedesEffect`). In the reversed
  order, which no source path runs, the two paths record different snapshots
  (`HookAfterEffectSkews`). Once registered, the tracker does not read the token
  (`TokenReadsIgnoredOnceRegistered`), and once `initL2` has run with the base token registered,
  the base token's first touch is the identity (`BaseNeverTakesLegacyPath`).
- **The base token and registration.** The inbound base path never changes a chain balance
  (`BaseFinalizeNeverCreditsChainBalance`); with a base token native to this chain the sentinel
  fails (`BaseTokenNativeAsymmetry`), which is why `Inv` has the premise `BaseNotSelfNative`.
  Registration is monotone and the snapshot is written once, except by the backfill
  (`RegistrationMonotone`), which writes only the base token's snapshot from a saved zero
  (`BackfillOnlyBaseFromZero`) and happens at most once (`BackfillAtMostOnce`).

Witnesses: `AccountingRunSatisfiable`, `TrackerRoundTripSatisfiable`, `BackfillSatisfiable`,
`FirstTouchSatisfiable`, `HookPrecedesEffectSatisfiable`, `BaseNeverLegacySatisfiable`,
`NativeEscrowSatisfiable` (a composed run from a fresh tracker after `initL2`, with a nonzero
vault balance before registration, a direct transfer into the vault after it, and nonzero flows
both ways). The countermodels are their own witnesses. No result takes a hash premise.

Model boundaries (`MODEL-L2-TRACKER` in the [assumption register](../../../ASSUMPTIONS.md)):
`block.chainid`, the system addresses and the vault's `originChainId`/`tokenAddress` entries are
a fixed `Config`; the settlement layer is changed by a step of its own. A revert is the absence of
a step. The token reads of a first touch are free inputs in `Accounting` and `HookOrdering`
(`HookOrdering` computes them from the token model's ledger), and the ledger is composed with
whole runs only in `NativeEscrow`, for one asset. Not modelled: the inherited ownership and pause
slots, events, `L2NativeTokenVault.updateL2` rewriting the base token's vault entries, upgrades
(`OPS-CONFIG`), the value movement of the base token through `BaseTokenHolder`, and the vault's own
other checks around a hook (router, pause, amount, asset id, WETH, `msg.value`). Fresh storage is the starting point of a newly deployed tracker only.

Later heads. At `draft/v0.35.0` `b17415d20` and `main` `70096e2ea` (the same tracker code,
which is also the file at the upgrade pin `e561b9cc2`), the backfill, `registerBaseTokenDuringUpgrade`
and `initL2`'s backfill flag are gone, and the new `assertRecoveryIsAccountingNeutral` reverts a
recovery whose original destination is L1, and one of a base token native to this chain; the L2
vault calls it before any refund. The registration and flow functions are the same code as at the
pin. No result here is checked against those heads.
