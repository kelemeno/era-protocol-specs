import EraSpec.Contracts.L2AssetTracker.Specs.LaterHeads

/-!
# Properties: the tracker results at the current heads, and what the recovery guard closes

Statements about `EraSpec.Contracts.L2AssetTracker.Specs.LaterHeads` (`draft/v0.35.0` at
`b17415d20`, and `main` at `70096e2ea`, whose tracker is the same code).  Proofs are in
`EraSpec.Contracts.L2AssetTracker.Proofs.LaterHeads`.

## The accounting results carry over

* `HeadStepIsPinStep`, `HeadRunIsPinRun`: from a state whose backfill flag is clear while
  `initL2` has not run (as in fresh storage, and in every state satisfying `Inv`), every call at
  the heads is a step of the pin model and every run at the heads a run of it.
* So `AccountingInvariant`, `NativeSentinel`, `InflowOverflowIsCap` and `OutflowIffNetOutFits`
  hold for runs at the heads: `HeadAccountingInvariant`, `HeadNativeSentinel`,
  `HeadInflowOverflowIsCap`, `HeadOutflowIffNetOutFits`; and `BaseNeverTakesLegacyPath` does too
  (`HeadBaseNeverTakesLegacyPath`).
* `HeadEscrowRunIsEscrowRun`: under the same premise on the starting state, a composed run with a
  native token at the heads (`HeadEscrowStep`) is a composed run of `Specs/NativeEscrow.lean`.  So
  the escrow results hold at the heads: `HeadEscrowInvariant`, `HeadNativeReleasesAreEscrowed`,
  `HeadNativeInboundIffCap`, `HeadFundedNativeOutboundSucceeds`.  The single-call statements of
  `Properties/HookOrdering.lean` are about the flow functions and the vault's paths, which are the
  pin's code at the heads, so they need no restatement; their recovery conjunct is the pin's
  recovery, which the heads run when the guard holds (`headRecover`).

## The recovery guard

* `HeadRecoveryRestoresVaultAndTracker` (headline): with the L2 hooks, after a successful
  preparation on a `WellFormed` vault state, the heads' recovery of the returned data, applied to
  the prepared state with only the settlement layer changed (to any layer), succeeds exactly when
  the guard holds (the destination is not L1, and the asset is not the tracker's base asset
  native here), and then it restores the vault state and the tracker's storage up to the
  first-touch registration of the asset.  At the pin there are recoveries to L1 that change both
  L1 counters (`NativeTokenVaultBase.L2L1DestinationCountersDiverge`) or, across a
  settlement-layer change, one of them (`L2SlSwitchBetweenPrepareAndRecover`); at the heads every
  recovery to L1 of a preparation's data reverts.
* `HeadGuardRejectsPinDivergence`: a state where the pin's recovery to L1 succeeds and leaves the
  state changed, while the heads' recovery of the same call reverts.

## Non-vacuity

`HeadRunSatisfiable` is a run at the heads from fresh storage satisfying `Inv`, through the heads'
`initL2`, in which a legacy native asset is registered by its first touch (so `E ≠ 0`) and has
nonzero outflow and inflow, and in which an inbound transfer within the cap succeeds and one
beyond it reverts: it meets the premises of the four transferred accounting results and of
`HeadRunIsPinRun`.  `HeadBaseNeverLegacySatisfiable` is a run at the heads from fresh storage
through `initL2` and the vault's registration of the base asset, then base-token flows both ways:
it meets the premises of `HeadBaseNeverTakesLegacyPath`.  `HeadNativeEscrowSatisfiable` is a
composed run at the heads from a fresh tracker next to a well-formed ledger in which the vault
already holds a nonzero balance, through the heads' `initL2`, to a state where the native asset is
registered with nonzero outflow and inflow, and where a funded outbound transfer and an inbound
transfer to a nonzero receiver both succeed: it meets the premises of the escrow results.
`HeadRecoverySatisfiable` meets those of `HeadRecoveryRestoresVaultAndTracker` with a nonzero
amount, an asset the tracker had not registered (so the registration is not the identity), a
settlement-layer change between the preparation and the recovery, and a successful recovery.
`HeadGuardRejectsPinDivergence` is its own witness.  No result takes a hash premise.
-/

namespace Contracts.L2AssetTracker

open Contracts.NativeTokenVaultBase (State Request Result prepare ResolutionCall L2Accounting l2Hooks
  l2ResolutionHooks bridgeRecoverFailedTransfer recoveryCall WellFormed Bytes)

/-! ## The accounting results carry over -/

/-- **A CALL AT THE HEADS IS A STEP OF THE PIN MODEL.**  From a state in which the backfill flag
is clear whenever `initL2` has not run, every successful call at the heads is a successful step of
`Specs/Accounting.lean` (the heads' `initL2` is the pin's `initL2` with a clear flag). -/
def Properties.HeadStepIsPinStep : Prop :=
  ∀ (cfg : Config) (sys sys' : Sys),
    (sys.st.guardInitialized = false → sys.st.needBaseTokenTotalSupplyBackfill = false) →
    HeadStep cfg sys sys' → Step cfg sys sys'

/-- **A RUN AT THE HEADS IS A RUN OF THE PIN MODEL.**  From a state in which the backfill flag is
clear whenever `initL2` has not run, every state reachable by calls at the heads is reachable by
steps of `Specs/Accounting.lean`. -/
def Properties.HeadRunIsPinRun : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys),
    (sys₀.st.guardInitialized = false → sys₀.st.needBaseTokenTotalSupplyBackfill = false) →
    HeadReach cfg sys₀ sys → Reach cfg sys₀ sys

/-- **THE INVARIANT HOLDS ALONG EVERY RUN AT THE HEADS.** -/
def Properties.HeadAccountingInvariant : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys), Inv cfg sys₀ → HeadReach cfg sys₀ sys → Inv cfg sys

/-- **WHAT THE CHAIN BALANCE OF A NATIVE TOKEN IS, AT THE HEADS.**  `Properties.NativeSentinel`
for runs at the heads: along every such run from a state satisfying `Inv`, for every registered
native asset `a`, with `E := MAX - snapshot`, `chainBalance + Σout = snapshot + Σin`,
`Σin ≤ E + Σout`, and `chainBalance = MAX - (E + Σout - Σin)`. -/
def Properties.HeadNativeSentinel : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys) (a : AssetId),
    Inv cfg sys₀ → HeadReach cfg sys₀ sys → sys.st.isAssetRegistered a = true → Native cfg a →
      (sys.st.chainBalance cfg.thisChain a).val + sys.audit.outflow a =
          (sys.st.totalPreV31TotalSupply a).amount.val + sys.audit.inflow a ∧
      sys.audit.inflow a ≤
          (MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply a).amount.val) +
            sys.audit.outflow a ∧
      (sys.st.chainBalance cfg.thisChain a).val =
          MAX_TOKEN_BALANCE.val -
            ((MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply a).amount.val) +
              sys.audit.outflow a - sys.audit.inflow a)

/-- **THE INBOUND CAP, AT THE HEADS.**  `Properties.InflowOverflowIsCap` for states reached by runs
at the heads: for a registered native asset whose inbound transfer touches no L1 counter, the
vault's `handleFinalizeBridgingOnL2` succeeds iff `Σin + amount ≤ E + Σout`. -/
def Properties.HeadInflowOverflowIsCap : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys) (reads : TokenReads) (fromChain : ChainId) (a : AssetId)
    (amount : UInt256),
    Inv cfg sys₀ → HeadReach cfg sys₀ sys → sys.st.isAssetRegistered a = true → Native cfg a →
    (fromChain ≠ sys.st.l1ChainId ∨ sys.sl ≠ sys.st.l1ChainId) →
      ((∃ sys', execHead cfg sys (.finalize reads fromChain a amount) = some sys') ↔
        sys.audit.inflow a + amount.val ≤
          (MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply a).amount.val) +
            sys.audit.outflow a)

/-- **THE OUTBOUND BOUND, AT THE HEADS.**  `Properties.OutflowIffNetOutFits` for states reached by
runs at the heads: for a registered native asset whose token address is set in the vault and an
outbound transfer touching no L1 counter, the vault's `handleInitiateBridgingOnL2` succeeds iff
`E + Σout + amount ≤ MAX + Σin`. -/
def Properties.HeadOutflowIffNetOutFits : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys) (reads : TokenReads) (toChain : ChainId) (a : AssetId)
    (amount : UInt256),
    Inv cfg sys₀ → HeadReach cfg sys₀ sys → sys.st.isAssetRegistered a = true → Native cfg a →
    cfg.ntvTokenAddress a ≠ 0 →
    (toChain ≠ sys.st.l1ChainId ∨ sys.sl ≠ sys.st.l1ChainId) →
      ((∃ sys', execHead cfg sys (.initiate reads toChain a amount) = some sys') ↔
        (MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply a).amount.val) +
            sys.audit.outflow a + amount.val ≤ MAX_TOKEN_BALANCE.val + sys.audit.inflow a)

/-- **THE BASE TOKEN NEVER TAKES THE FIRST-TOUCH PATH, AT THE HEADS.**
`Properties.BaseNeverTakesLegacyPath` for runs at the heads: along any run at the heads from a
state where `initL2` has run and the base token is registered, the base asset id never changes, it
stays registered, and its first-touch registration is the identity for every token read and token
address. -/
def Properties.HeadBaseNeverTakesLegacyPath : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys), HeadReach cfg sys₀ sys →
    sys₀.st.guardInitialized = true →
    sys₀.st.isAssetRegistered sys₀.st.baseTokenAssetId = true →
      sys.st.baseTokenAssetId = sys₀.st.baseTokenAssetId ∧
      sys.st.isAssetRegistered sys.st.baseTokenAssetId = true ∧
      ∀ (reads : TokenReads) (token : Address),
        registerLegacyTokenIfNeeded cfg sys.st reads sys.st.baseTokenAssetId token = some sys.st

/-! ## The composed run with a native token, at the heads -/

/-- **A COMPOSED RUN AT THE HEADS IS A COMPOSED RUN OF THE PIN MODEL.**  From a state in which the
backfill flag is clear whenever `initL2` has not run, every state reachable by `HeadEscrowStep`s is
reachable by `EscrowStep`s (`Specs/NativeEscrow.lean`). -/
def Properties.HeadEscrowRunIsEscrowRun : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys),
    (e₀.sys.st.guardInitialized = false → e₀.sys.st.needBaseTokenTotalSupplyBackfill = false) →
    HeadEscrowReach cfg a e₀ e → EscrowReach cfg a e₀ e

/-- **THE ESCROW INVARIANT HOLDS ALONG EVERY COMPOSED RUN AT THE HEADS.**  For an asset `a` native
here, from a state satisfying `EscrowInv`, every state reachable by `HeadEscrowStep`s satisfies
`EscrowInv`. -/
def Properties.HeadEscrowInvariant : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys), Native cfg a →
    EscrowInv cfg a e₀ → HeadEscrowReach cfg a e₀ e → EscrowInv cfg a e

/-- **WHAT THE TRACKER CAN LET IN IS IN THE VAULT, AT THE HEADS.**
`Properties.NativeReleasesAreEscrowed` for composed runs at the heads: for a registered asset `a`
native here, with `E := MAX - snapshot`, `MAX - chainBalance` is at most the vault's balance of
the token, and so is `E + Σout - Σin`. -/
def Properties.HeadNativeReleasesAreEscrowed : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys), Native cfg a →
    EscrowInv cfg a e₀ → HeadEscrowReach cfg a e₀ e → e.sys.st.isAssetRegistered a = true →
      MAX_TOKEN_BALANCE.val - (e.sys.st.chainBalance cfg.thisChain a).val ≤
          e.tok.balances cfg.ntv ∧
      (MAX_TOKEN_BALANCE.val - (e.sys.st.totalPreV31TotalSupply a).amount.val) +
          e.sys.audit.outflow a - e.sys.audit.inflow a ≤ e.tok.balances cfg.ntv

/-- **AN INBOUND NATIVE TRANSFER SUCCEEDS EXACTLY WITHIN THE CAP, AT THE HEADS.**
`Properties.NativeInboundIffCap` for composed runs at the heads: for a registered asset `a` native
here, a nonzero vault address and a nonzero receiver, and an inbound transfer touching no L1
counter, the vault's inbound native path (hook, then withdrawal) succeeds iff
`Σin + amount ≤ E + Σout`. -/
def Properties.HeadNativeInboundIffCap : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys) (chain : ChainId) (account : Address)
    (amount : UInt256),
    Native cfg a → EscrowInv cfg a e₀ → HeadEscrowReach cfg a e₀ e →
    e.sys.st.isAssetRegistered a = true → cfg.ntv ≠ 0 → account ≠ 0 →
    (chain ≠ e.sys.st.l1ChainId ∨ e.sys.sl ≠ e.sys.st.l1ChainId) →
      ((∃ x, runPath cfg .nativeIn e.sys.st e.sys.sl e.tok chain a account amount = some x) ↔
        e.sys.audit.inflow a + amount.val ≤
          (MAX_TOKEN_BALANCE.val - (e.sys.st.totalPreV31TotalSupply a).amount.val) +
            e.sys.audit.outflow a)

/-- **A FUNDED OUTBOUND NATIVE TRANSFER GOES THROUGH, AT THE HEADS.**
`Properties.FundedNativeOutboundSucceeds` for composed runs at the heads: for an asset `a` native
here (registered or not) whose token address in the vault is set, on a chain with nonzero id and a
nonzero vault address, every depositor other than the vault and the zero address holding at least
`amount` can move it out on the outbound native path, unless a transfer to L1 while the chain
settles on L1 would raise `totalWithdrawalsToL1` past `2^256 - 1`.  Allowances are not modelled. -/
def Properties.HeadFundedNativeOutboundSucceeds : Prop :=
  ∀ (cfg : Config) (a : AssetId) (e₀ e : EscrowSys) (chain : ChainId) (account : Address)
    (amount : UInt256),
    Native cfg a → EscrowInv cfg a e₀ → HeadEscrowReach cfg a e₀ e →
    cfg.thisChain ≠ 0 → cfg.ntvTokenAddress a ≠ 0 → cfg.ntv ≠ 0 →
    account ≠ 0 → account ≠ cfg.ntv → amount.val ≤ e.tok.balances account →
    (chain = e.sys.st.l1ChainId ∧ e.sys.sl = e.sys.st.l1ChainId →
      (e.sys.st.interopInfo a).totalWithdrawalsToL1.val + amount.val < UInt256.size) →
      ∃ x, runPath cfg .nativeOut e.sys.st e.sys.sl e.tok chain a account amount = some x

/-! ## The recovery guard -/

/-- **AT THE HEADS, A RECOVERY OF A PREPARED TRANSFER REVERTS OR RESTORES, ON ANY SETTLEMENT
LAYER** (headline).  With the L2 hooks, on a `WellFormed` vault state `s`, after a successful
preparation (whose asset is then not the vault's base asset, the case `headRecover` describes):
the tracker's first-touch registration of the asset from the starting tracker storage and the
pre-burn token is defined, with result `st₀`, which is the starting storage if the asset was
registered; and for every settlement layer `sl₂`, the heads' recovery (`headRecover`) of the
returned data (`recoveryCall`), applied to the prepared state moved to `sl₂`, succeeds iff the
guard holds of the starting tracker storage (the destination is not L1, and the asset is not the
tracker's base asset native here), and then yields the original vault state with tracker storage
`st₀` and settlement layer `sl₂`. -/
def Properties.HeadRecoveryRestoresVaultAndTracker : Prop :=
  ∀ (cfg : Config) (metadata : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting) (r : Request) (out : Result L2Accounting) (sl₂ : ChainId),
    WellFormed s → prepare (l2Hooks cfg metadata) s r = some out →
      ∃ st₀, registerLegacyTokenIfNeeded cfg s.accounting.st (tokenReads cfg s.token) r.assetId
          (cfg.ntvTokenAddress r.assetId) = some st₀ ∧
        (s.accounting.st.isAssetRegistered r.assetId = true → st₀ = s.accounting.st) ∧
        headRecover cfg { out.state with accounting := { out.state.accounting with sl := sl₂ } }
            (recoveryCall s.config.router r out.data) =
          if RecoveryAccountingNeutral cfg s.accounting.st r.assetId r.destinationChain then
            some { s with accounting := ⟨st₀, sl₂⟩ }
          else none

/-- **THE GUARD CLOSES THE PIN'S L1 DIVERGENCE.**  A `WellFormed` vault state whose tracker has the
asset registered, and a successful preparation of a nonzero amount to L1 while the chain settles
on L1, after which the pin's recovery of the returned data succeeds with a state different from
the original one, and the heads' recovery of the same call reverts. -/
def Properties.HeadGuardRejectsPinDivergence : Prop :=
  ∃ (cfg : Config) (metadata : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting) (r : Request) (out : Result L2Accounting) (t : State L2Accounting),
    WellFormed s ∧ s.accounting.st.isAssetRegistered r.assetId = true ∧
    r.destinationChain = s.accounting.st.l1ChainId ∧ s.accounting.sl = s.accounting.st.l1ChainId ∧
    prepare (l2Hooks cfg metadata) s r = some out ∧ r.data.amount ≠ 0 ∧
    bridgeRecoverFailedTransfer (l2ResolutionHooks cfg) out.state
      (recoveryCall s.config.router r out.data) = some t ∧ t ≠ s ∧
    headRecover cfg out.state (recoveryCall s.config.router r out.data) = none

/-! ## Non-vacuity -/

/-- **A RUN AT THE HEADS MEETING THE PREMISES OF THE TRANSFERRED RESULTS.**  From fresh storage
satisfying `Inv`, a run at the heads through the heads' `initL2` to a state where a native asset
`a`, with a token address in the vault and a nonzero `E`, is registered with nonzero outflow and
inflow; for a chain `c` that is not L1, an inbound transfer of `a` from `c` succeeds for one amount
and reverts for another. -/
def Properties.HeadRunSatisfiable : Prop :=
  ∃ (cfg : Config) (sl : ChainId) (sys : Sys) (reads : TokenReads) (c : ChainId) (a : AssetId)
    (small large : UInt256),
    Inv cfg (Sys.fresh sl) ∧ HeadReach cfg (Sys.fresh sl) sys ∧ sys.st.guardInitialized = true ∧
    sys.st.isAssetRegistered a = true ∧ Native cfg a ∧ cfg.ntvTokenAddress a ≠ 0 ∧
    c ≠ sys.st.l1ChainId ∧
    0 < sys.audit.outflow a ∧ 0 < sys.audit.inflow a ∧
    0 < MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply a).amount.val ∧
    (∃ sys', execHead cfg sys (.finalize reads c a small) = some sys') ∧
    execHead cfg sys (.finalize reads c a large) = none

/-- **A RUN AT THE HEADS WITH BASE-TOKEN FLOWS.**  From fresh storage satisfying `Inv`: the heads'
`initL2`, the vault's `registerNewTokenIfNeeded` of the base asset (the heads' genesis registration,
`L2NTVH:118-123`), reaching a state where `initL2` has run and the base token is registered; then
the run moves the base token out and back in. -/
def Properties.HeadBaseNeverLegacySatisfiable : Prop :=
  ∃ (cfg : Config) (sl : ChainId) (sys₀ sys₁ sys₂ : Sys) (reads : TokenReads) (c : ChainId),
    Inv cfg (Sys.fresh sl) ∧ HeadReach cfg (Sys.fresh sl) sys₀ ∧
    sys₀.st.guardInitialized = true ∧
    sys₀.st.isAssetRegistered sys₀.st.baseTokenAssetId = true ∧
    execHead cfg sys₀ (.initiateBase reads c 1) = some sys₁ ∧
    execHead cfg sys₁ (.finalizeBase reads cfg.baseTokenHolder c 1) = some sys₂ ∧
    HeadReach cfg sys₀ sys₂

/-- **A NONTRIVIAL COMPOSED RUN AT THE HEADS.**  A fresh tracker next to a well-formed ledger in
which the vault already holds a nonzero balance; a composed run at the heads to `e` in which
`initL2` has run and the native asset `a` is registered, with nonzero outflow and inflow, and in
which the vault's balance strictly exceeds `MAX - chainBalance`; at `e`, a depositor other than the
vault holding a nonzero `amount` can move it out to a chain that is not L1, and an inbound transfer
of `amount` from that chain to a nonzero receiver succeeds. -/
def Properties.HeadNativeEscrowSatisfiable : Prop :=
  ∃ (cfg : Config) (a : AssetId) (sl : ChainId) (tok₀ : Contracts.BridgedStandardERC20.State)
    (e : EscrowSys) (chain : ChainId) (account receiver : Address) (amount : UInt256),
    Native cfg a ∧ cfg.thisChain ≠ 0 ∧ cfg.ntvTokenAddress a ≠ 0 ∧ cfg.ntv ≠ 0 ∧
    EscrowInv cfg a ⟨Sys.fresh sl, tok₀⟩ ∧ HeadEscrowReach cfg a ⟨Sys.fresh sl, tok₀⟩ e ∧
    0 < tok₀.balances cfg.ntv ∧
    e.sys.st.guardInitialized = true ∧ e.sys.st.isAssetRegistered a = true ∧
    0 < e.sys.audit.outflow a ∧ 0 < e.sys.audit.inflow a ∧
    MAX_TOKEN_BALANCE.val - (e.sys.st.chainBalance cfg.thisChain a).val < e.tok.balances cfg.ntv ∧
    account ≠ 0 ∧ account ≠ cfg.ntv ∧ receiver ≠ 0 ∧ amount ≠ 0 ∧
    amount.val ≤ e.tok.balances account ∧ chain ≠ e.sys.st.l1ChainId ∧
    (∃ x, runPath cfg .nativeOut e.sys.st e.sys.sl e.tok chain a account amount = some x) ∧
    (∃ x, runPath cfg .nativeIn e.sys.st e.sys.sl e.tok chain a receiver amount = some x)

/-- **THE HEADLINE'S PREMISES, WITH A REAL REGISTRATION AND A SETTLEMENT-LAYER CHANGE.**  A
`WellFormed` vault state whose tracker storage has been initialized and has not registered the
asset, a successful preparation of a nonzero amount that passes the guard, a settlement layer
`sl₂` other than the one at the preparation, and a successful recovery by the heads after the
change, whose tracker storage differs from the starting one. -/
def Properties.HeadRecoverySatisfiable : Prop :=
  ∃ (cfg : Config) (metadata : Contracts.BridgedStandardERC20.State → UInt256 → Option Bytes)
    (s : State L2Accounting) (r : Request) (out : Result L2Accounting) (sl₂ : ChainId)
    (t : State L2Accounting),
    WellFormed s ∧ prepare (l2Hooks cfg metadata) s r = some out ∧ r.data.amount ≠ 0 ∧
    s.accounting.st.guardInitialized = true ∧ s.accounting.st.isAssetRegistered r.assetId = false ∧
    RecoveryAccountingNeutral cfg s.accounting.st r.assetId r.destinationChain ∧
    sl₂ ≠ s.accounting.sl ∧
    headRecover cfg { out.state with accounting := { out.state.accounting with sl := sl₂ } }
      (recoveryCall s.config.router r out.data) = some t ∧
    t.accounting.st ≠ s.accounting.st

end Contracts.L2AssetTracker
