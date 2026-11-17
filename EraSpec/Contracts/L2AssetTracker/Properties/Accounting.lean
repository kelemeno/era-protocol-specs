import EraSpec.Contracts.L2AssetTracker.Specs.Accounting

/-!
# Properties: what `chainBalance` means, the release cap, registration, and the round trip

Statements about `EraSpec.Contracts.L2AssetTracker.Specs.Accounting`.  Proofs are in
`EraSpec.Contracts.L2AssetTracker.Proofs.Accounting`.  `TRK` is
`bridge/asset-tracker/L2AssetTracker.sol` at pin `c67894b9`.

## The chain balance is a sentinel, and a cap

* `AccountingInvariant`: `Inv` holds along every run from a state satisfying it, and
  `FreshTrackerSatisfiesInv` gives the deployed starting point.
* `NativeSentinel` (headline): for every registered native asset,
  `chainBalance + Σout = snapshot + Σin`, so `chainBalance = MAX - (E + Σout - Σin)` where
  `E = MAX - snapshot` is `0` for a token registered as new and, for a legacy one, the vault's
  balance as the first touch read it; and `Σin ≤ E + Σout`.
* `InflowOverflowIsCap`: for a registered native asset, an inbound transfer touching no L1 counter
  succeeds iff `Σin + amount ≤ E + Σout`; beyond that the checked `+=` at `TRK:296` reverts.
  `ChainBalanceGatesInflow` is a run in which the same inbound transfer reverts before an
  outbound one and succeeds after it.
* `OutflowIffNetOutFits`: in the same setting, an outbound transfer succeeds iff
  `E + Σout + amount ≤ MAX + Σin`.  In the tracker alone the amounts are free inputs; run
  together with the token's ledger, a funded outbound transfer never fails on the chain balance
  (`Properties/NativeEscrow.lean`, `FundedNativeOutboundSucceeds`).
* `TokenReadsIgnoredOnceRegistered`: for a registered asset the vault's two flow calls do not
  depend on the token reads.  So once an asset is registered, a transfer straight into the vault
  changes neither its chain balance nor the cap; one made before a legacy first touch is part of
  the `E` that touch reads (`TRK:325-326`).

## The round trip

* `TrackerHooksCancelOffL1`: an outbound call (vault hook, `TRK:221-250`) followed by an inbound
  one of the same chain, asset and amount (`TRK:269-305`) restores the storage exactly, up to the
  first-touch registration of the asset, when the chain is not L1 or the chain settles off L1 at
  both calls.  `NativeTokenVaultBase.L2HooksCancelModuloRegistration` is this law for the vault's
  hooks.
* `L1CountersMoveTogether`: when the chain is L1 and the chain settles on L1 at both calls, the
  same round trip raises both `totalWithdrawalsToL1` and `totalSuccessfulDepositsFromL1` by the
  amount, so neither counter is restored.

## The base token

* `BaseFinalizeNeverCreditsChainBalance`: a successful `handleFinalizeBaseTokenBridgingOnL2`
  leaves every chain balance unchanged once the base token is registered, native or not
  (`TRK:377` passes `_isNativeToThisChain: false`).  The outbound base path does debit a native
  base token (`TRK:256-260`).
* `BaseTokenNativeAsymmetry` (countermodel): with a base token native to this chain, an outbound
  and an inbound base transfer of the same amount leave the chain balance lowered by the amount,
  and the sentinel fails.  So the premise `BaseNotSelfNative` of `Inv` is needed.

## Registration and the backfill

* `RegistrationMonotone`: a registered asset stays registered along any run; across one step its
  snapshot changes only if the step clears the backfill flag, at the base token's saved zero
  snapshot.
* `BackfillOnlyBaseFromZero`: a backfill writes only the base token's snapshot, from a saved
  zero, and clears its flag.
* `BackfillAtMostOnce`: after one backfill no later one succeeds, on any run from a state
  satisfying `Inv`.

## Non-vacuity

`AccountingRunSatisfiable` is a run from fresh storage to a state where two native assets are
registered, one with nonzero outflow and inflow and one whose `E` is nonzero, with nonzero
outflow; it meets the premises of `NativeSentinel`, `InflowOverflowIsCap` and
`OutflowIffNetOutFits`, with an inbound amount accepted and a larger one rejected.
`TrackerRoundTripSatisfiable` meets the premises of `TrackerHooksCancelOffL1` on an unregistered
native asset, after `initL2` (so the call registers it and moves its chain balance), and those of
`L1CountersMoveTogether` on a registered native asset.  `BackfillSatisfiable` is a run with a
successful backfill.  The countermodels are their own witnesses.
-/

namespace Contracts.L2AssetTracker

/-! ## The invariant -/

/-- **THE INVARIANT HOLDS ALONG EVERY RUN.**  From a state satisfying `Inv`, every state reachable
by successful calls (any entry point, by its permitted caller, with any token reads, and any
change of settlement layer) satisfies `Inv`. -/
def Properties.AccountingInvariant : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys), Inv cfg sys₀ → Reach cfg sys₀ sys → Inv cfg sys

/-- **THE FRESH STARTING POINT.**  Fresh storage with an empty audit satisfies `Inv`, on any
settlement layer, when neither the base asset the upgrader will install nor the zero asset id
(the base asset id before `initL2`) is native here.  Fresh storage is where a newly deployed
tracker starts; a tracker upgraded in place keeps the storage it had (`TRK:32-35`), and a run from
it needs a starting state satisfying `Inv` instead. -/
def Properties.FreshTrackerSatisfiesInv : Prop :=
  ∀ (cfg : Config) (sl : ChainId), ¬ Native cfg cfg.initBaseAssetId → ¬ Native cfg 0 →
    Inv cfg (Sys.fresh sl)

/-- **WHAT THE CHAIN BALANCE OF A NATIVE TOKEN IS** (headline).  Along every run from a state
satisfying `Inv`, for every registered native asset `a` with snapshot `snap` and
`E := MAX - snap`: the chain balance plus everything bridged out equals the snapshot plus
everything bridged in; no more has come in than `E` plus what went out; and
`chainBalance = MAX - (E + Σout - Σin)`. -/
def Properties.NativeSentinel : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys) (a : AssetId),
    Inv cfg sys₀ → Reach cfg sys₀ sys → sys.st.isAssetRegistered a = true → Native cfg a →
      (sys.st.chainBalance cfg.thisChain a).val + sys.audit.outflow a =
          (sys.st.totalPreV31TotalSupply a).amount.val + sys.audit.inflow a ∧
      sys.audit.inflow a ≤
          (MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply a).amount.val) +
            sys.audit.outflow a ∧
      (sys.st.chainBalance cfg.thisChain a).val =
          MAX_TOKEN_BALANCE.val -
            ((MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply a).amount.val) +
              sys.audit.outflow a - sys.audit.inflow a)

/-- **THE INBOUND NATIVE TRANSFER IS CAPPED BY WHAT WENT OUT.**  In a state reached from one
satisfying `Inv`, for a registered native asset whose inbound transfer touches no L1 counter (the
source chain is not L1, or the chain does not settle on L1): the vault's
`handleFinalizeBridgingOnL2` succeeds iff `Σin + amount ≤ E + Σout`. -/
def Properties.InflowOverflowIsCap : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys) (reads : TokenReads) (fromChain : ChainId) (a : AssetId)
    (amount : UInt256),
    Inv cfg sys₀ → Reach cfg sys₀ sys → sys.st.isAssetRegistered a = true → Native cfg a →
    (fromChain ≠ sys.st.l1ChainId ∨ sys.sl ≠ sys.st.l1ChainId) →
      ((∃ sys', exec cfg sys (.finalize reads fromChain a amount) = some sys') ↔
        sys.audit.inflow a + amount.val ≤
          (MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply a).amount.val) +
            sys.audit.outflow a)

/-- **THE OUTBOUND NATIVE TRANSFER FAILS ONLY IF THE NET AMOUNT OUT WOULD NOT FIT IN A WORD.**  In
the same setting, for an asset the vault knows (`tokenAddress` set) and an outbound transfer
touching no L1 counter: the vault's `handleInitiateBridgingOnL2` succeeds iff
`E + Σout + amount ≤ MAX + Σin`. -/
def Properties.OutflowIffNetOutFits : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys) (reads : TokenReads) (toChain : ChainId) (a : AssetId)
    (amount : UInt256),
    Inv cfg sys₀ → Reach cfg sys₀ sys → sys.st.isAssetRegistered a = true → Native cfg a →
    cfg.ntvTokenAddress a ≠ 0 →
    (toChain ≠ sys.st.l1ChainId ∨ sys.sl ≠ sys.st.l1ChainId) →
      ((∃ sys', exec cfg sys (.initiate reads toChain a amount) = some sys') ↔
        (MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply a).amount.val) +
            sys.audit.outflow a + amount.val ≤ MAX_TOKEN_BALANCE.val + sys.audit.inflow a)

/-- **ONCE REGISTERED, THE TRACKER DOES NOT READ THE TOKEN.**  For a registered asset, the vault's
outbound and inbound calls give the same result whatever the token reads are. -/
def Properties.TokenReadsIgnoredOnceRegistered : Prop :=
  ∀ (cfg : Config) (st : Storage) (sl : ChainId) (reads reads' : TokenReads) (c : ChainId)
    (a : AssetId) (amount : UInt256),
    st.isAssetRegistered a = true →
      handleInitiateBridgingOnL2 cfg st sl reads cfg.ntv c a amount (cfg.ntvOriginChainId a) =
        handleInitiateBridgingOnL2 cfg st sl reads' cfg.ntv c a amount (cfg.ntvOriginChainId a) ∧
      handleFinalizeBridgingOnL2 cfg st sl reads cfg.ntv c a amount (cfg.ntvOriginChainId a)
          (cfg.ntvTokenAddress a) =
        handleFinalizeBridgingOnL2 cfg st sl reads' cfg.ntv c a amount (cfg.ntvOriginChainId a)
          (cfg.ntvTokenAddress a)

/-- **THE CHAIN BALANCE DECIDES AN INBOUND TRANSFER.**  From fresh storage, after the vault
registers a native asset as new, an inbound transfer of one unit from a chain that is not L1
reverts; after an outbound transfer of one unit to that chain, the same inbound transfer
succeeds. -/
def Properties.ChainBalanceGatesInflow : Prop :=
  ∃ (cfg : Config) (sl : ChainId) (reads : TokenReads) (c : ChainId) (a : AssetId)
    (sys₁ sys₂ sys₃ : Sys),
    Inv cfg (Sys.fresh sl) ∧ Native cfg a ∧ c ≠ sys₁.st.l1ChainId ∧
    exec cfg (Sys.fresh sl) (.registerNewToken a) = some sys₁ ∧
    exec cfg sys₁ (.finalize reads c a 1) = none ∧
    exec cfg sys₁ (.initiate reads c a 1) = some sys₂ ∧
    exec cfg sys₂ (.finalize reads c a 1) = some sys₃

/-! ## The round trip -/

/-- **OUT THEN IN, OFF L1: EVERYTHING IS RESTORED BUT THE REGISTRATION.**  If the vault's
outbound call `handleInitiateBridgingOnL2(c, a, amount, originChainId[a])` on storage `st` (with
settlement layer `sl₁` and token reads `reads₁`) succeeds with `st'`, and `c` is not L1 or the
chain settles off L1 at both calls (`sl₁`, `sl₂`), then the first-touch registration of `a` from
`st` with `reads₁` is defined, with result `st₀`, and the vault's inbound call
`handleFinalizeBridgingOnL2(c, a, amount, originChainId[a], tokenAddress[a])` on `st'` (any
reads, settlement layer `sl₂`) succeeds with exactly `st₀`.  If `a` was registered, `st₀ = st`. -/
def Properties.TrackerHooksCancelOffL1 : Prop :=
  ∀ (cfg : Config) (st st' : Storage) (sl₁ sl₂ : ChainId) (reads₁ reads₂ : TokenReads)
    (c : ChainId) (a : AssetId) (amount : UInt256),
    handleInitiateBridgingOnL2 cfg st sl₁ reads₁ cfg.ntv c a amount (cfg.ntvOriginChainId a) =
      some st' →
    (c ≠ st.l1ChainId ∨ (sl₁ ≠ st.l1ChainId ∧ sl₂ ≠ st.l1ChainId)) →
      ∃ st₀, registerLegacyTokenIfNeeded cfg st reads₁ a (cfg.ntvTokenAddress a) = some st₀ ∧
        handleFinalizeBridgingOnL2 cfg st' sl₂ reads₂ cfg.ntv c a amount (cfg.ntvOriginChainId a)
          (cfg.ntvTokenAddress a) = some st₀ ∧
        (st.isAssetRegistered a = true → st₀ = st)

/-- **OUT THEN IN, ON L1: BOTH L1 COUNTERS GROW.**  With `c = L1_CHAIN_ID` and the chain settling
on L1 at both calls, after a successful outbound call from `st`: the first-touch registration of
`a` from `st` is defined, with result `st₀`, and the outbound call did not overflow
`totalWithdrawalsToL1`; and unless `totalSuccessfulDepositsFromL1` would overflow, the inbound call
of the same chain, asset and amount succeeds, with the chain balances, registrations and snapshots
of `st₀`, the other assets' counters of `st₀`, and both of `a`'s counters raised by `amount`. -/
def Properties.L1CountersMoveTogether : Prop :=
  ∀ (cfg : Config) (st st' : Storage) (reads₁ reads₂ : TokenReads) (c : ChainId) (a : AssetId)
    (amount : UInt256),
    handleInitiateBridgingOnL2 cfg st st.l1ChainId reads₁ cfg.ntv c a amount
        (cfg.ntvOriginChainId a) = some st' →
    c = st.l1ChainId →
      ∃ st₀, registerLegacyTokenIfNeeded cfg st reads₁ a (cfg.ntvTokenAddress a) = some st₀ ∧
        (st₀.interopInfo a).totalWithdrawalsToL1.val + amount.val < UInt256.size ∧
        ((st₀.interopInfo a).totalSuccessfulDepositsFromL1.val + amount.val < UInt256.size →
          ∃ st₂, handleFinalizeBridgingOnL2 cfg st' st.l1ChainId reads₂ cfg.ntv c a amount
              (cfg.ntvOriginChainId a) (cfg.ntvTokenAddress a) = some st₂ ∧
            (st₂.interopInfo a).totalWithdrawalsToL1.val =
              (st₀.interopInfo a).totalWithdrawalsToL1.val + amount.val ∧
            (st₂.interopInfo a).totalSuccessfulDepositsFromL1.val =
              (st₀.interopInfo a).totalSuccessfulDepositsFromL1.val + amount.val ∧
            st₂.chainBalance = st₀.chainBalance ∧
            st₂.isAssetRegistered = st₀.isAssetRegistered ∧
            st₂.totalPreV31TotalSupply = st₀.totalPreV31TotalSupply ∧
            ∀ b, b ≠ a → st₂.interopInfo b = st₀.interopInfo b)

/-! ## The base token -/

/-- **THE INBOUND BASE PATH NEVER CREDITS THE CHAIN BALANCE.**  For a registered base token, a
successful `handleFinalizeBaseTokenBridgingOnL2` leaves every chain balance unchanged, whether or
not the base token is native here. -/
def Properties.BaseFinalizeNeverCreditsChainBalance : Prop :=
  ∀ (cfg : Config) (st st' : Storage) (sl : ChainId) (reads : TokenReads) (caller : Address)
    (fromChain : ChainId) (amount : UInt256),
    st.isAssetRegistered st.baseTokenAssetId = true →
    handleFinalizeBaseTokenBridgingOnL2 cfg st sl reads caller fromChain amount = some st' →
      st'.chainBalance = st.chainBalance

/-- **COUNTERMODEL: `BaseNotSelfNative` IS NEEDED.**  With a base token native to this chain
(registered, with chain balance `MAX`), an outbound base transfer of one unit followed by an
inbound one of one unit, from a chain that is not L1, both succeed and leave the chain balance at
`MAX - 1`; `ChainBalanceSentinel` held before and fails after. -/
def Properties.BaseTokenNativeAsymmetry : Prop :=
  ∃ (cfg : Config) (sys₀ sys₁ sys₂ : Sys) (reads : TokenReads) (c : ChainId),
    Native cfg sys₀.st.baseTokenAssetId ∧
    sys₀.st.isAssetRegistered sys₀.st.baseTokenAssetId = true ∧
    sys₀.st.chainBalance cfg.thisChain sys₀.st.baseTokenAssetId = MAX_TOKEN_BALANCE ∧
    ChainBalanceSentinel cfg sys₀ sys₀.st.baseTokenAssetId ∧ c ≠ sys₀.st.l1ChainId ∧
    exec cfg sys₀ (.initiateBase reads c 1) = some sys₁ ∧
    exec cfg sys₁ (.finalizeBase reads cfg.baseTokenHolder c 1) = some sys₂ ∧
    (sys₂.st.chainBalance cfg.thisChain sys₀.st.baseTokenAssetId).val =
      MAX_TOKEN_BALANCE.val - 1 ∧
    ¬ ChainBalanceSentinel cfg sys₂ sys₀.st.baseTokenAssetId

/-! ## Registration and the backfill -/

/-- **REGISTRATION IS MONOTONE, AND THE SNAPSHOT IS WRITTEN ONCE.**  Along any run, a registered
asset stays registered.  Across any single step, a registered asset's snapshot is unchanged, or
the asset is the base token, its snapshot was the saved zero, and the step cleared the backfill
flag. -/
def Properties.RegistrationMonotone : Prop :=
  ∀ (cfg : Config),
    (∀ (sys sys' : Sys) (a : AssetId), Reach cfg sys sys' →
      sys.st.isAssetRegistered a = true → sys'.st.isAssetRegistered a = true) ∧
    (∀ (sys sys' : Sys) (a : AssetId), Step cfg sys sys' → sys.st.isAssetRegistered a = true →
      sys'.st.totalPreV31TotalSupply a = sys.st.totalPreV31TotalSupply a ∨
      (a = sys.st.baseTokenAssetId ∧ sys.st.totalPreV31TotalSupply a = ⟨true, 0⟩ ∧
        sys.st.needBaseTokenTotalSupplyBackfill = true ∧
        sys'.st.needBaseTokenTotalSupplyBackfill = false))

/-- **THE BACKFILL WRITES ONLY THE BASE TOKEN'S SNAPSHOT, FROM ZERO.**  A successful backfill
found the base token registered with a saved zero snapshot and the flag set; it writes the
snapshot's amount, clears the flag, and changes nothing else. -/
def Properties.BackfillOnlyBaseFromZero : Prop :=
  ∀ (cfg : Config) (sys sys' : Sys) (amount : UInt256),
    exec cfg sys (.backfill amount) = some sys' →
      sys.st.isAssetRegistered sys.st.baseTokenAssetId = true ∧
      sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId = ⟨true, 0⟩ ∧
      sys.st.needBaseTokenTotalSupplyBackfill = true ∧
      sys'.st = { sys.st with
        totalPreV31TotalSupply := Function.update sys.st.totalPreV31TotalSupply
          sys.st.baseTokenAssetId ⟨true, amount⟩
        needBaseTokenTotalSupplyBackfill := false } ∧
      sys'.sl = sys.sl ∧ sys'.audit = sys.audit

/-- **AT MOST ONE BACKFILL.**  From a state satisfying `Inv`, after a successful backfill, no
backfill succeeds in any later state of the run. -/
def Properties.BackfillAtMostOnce : Prop :=
  ∀ (cfg : Config) (sys₀ sys₁ sys₂ : Sys) (amount amount' : UInt256),
    Inv cfg sys₀ → exec cfg sys₀ (.backfill amount) = some sys₁ → Reach cfg sys₁ sys₂ →
      exec cfg sys₂ (.backfill amount') = none

/-! ## Non-vacuity -/

/-- **THE SENTINEL AND CAP PREMISES ON A NONTRIVIAL RUN.**  From fresh storage satisfying `Inv`,
a run to a state where two distinct native assets `a` and `b`, both with a token address in the
vault, are registered; `a` has nonzero outflow and inflow, `b` has nonzero outflow and a nonzero
`E`; a chain `c` is not L1; and an inbound transfer of `b` from `c` succeeds for one amount and
reverts for another. -/
def Properties.AccountingRunSatisfiable : Prop :=
  ∃ (cfg : Config) (sl : ChainId) (sys : Sys) (reads : TokenReads) (c : ChainId)
    (a b : AssetId) (small large : UInt256),
    Inv cfg (Sys.fresh sl) ∧ Reach cfg (Sys.fresh sl) sys ∧ a ≠ b ∧
    sys.st.isAssetRegistered a = true ∧ sys.st.isAssetRegistered b = true ∧
    Native cfg a ∧ Native cfg b ∧ cfg.ntvTokenAddress a ≠ 0 ∧ cfg.ntvTokenAddress b ≠ 0 ∧
    c ≠ sys.st.l1ChainId ∧
    0 < sys.audit.outflow a ∧ 0 < sys.audit.inflow a ∧ 0 < sys.audit.outflow b ∧
    0 < MAX_TOKEN_BALANCE.val - (sys.st.totalPreV31TotalSupply b).amount.val ∧
    (∃ sys', exec cfg sys (.finalize reads c b small) = some sys') ∧
    exec cfg sys (.finalize reads c b large) = none

/-- **THE ROUND-TRIP PREMISES, WITH A REAL REGISTRATION AND WITH THE L1 COUNTERS.**  For a native
asset `a`: storage whose guard shows `initL2` has run, in which `a` is unregistered, and an
outbound call of a nonzero amount to a chain that is not L1 that succeeds (so it registers `a`);
and storage whose guard shows `initL2` has run, in which `a` is registered, an outbound call to L1
while settling on L1 that succeeds, and room in the deposit counter. -/
def Properties.TrackerRoundTripSatisfiable : Prop :=
  ∃ (cfg : Config) (st st' st₁ st₁' : Storage) (sl : ChainId) (reads : TokenReads)
    (c c' : ChainId) (a : AssetId) (amount : UInt256),
    Native cfg a ∧ st.guardInitialized = true ∧ st₁.guardInitialized = true ∧
    st.isAssetRegistered a = false ∧ c ≠ st.l1ChainId ∧ amount ≠ 0 ∧
    handleInitiateBridgingOnL2 cfg st sl reads cfg.ntv c a amount (cfg.ntvOriginChainId a) =
      some st' ∧
    st₁.isAssetRegistered a = true ∧ c' = st₁.l1ChainId ∧
    handleInitiateBridgingOnL2 cfg st₁ st₁.l1ChainId reads cfg.ntv c' a amount
      (cfg.ntvOriginChainId a) = some st₁' ∧
    (st₁.interopInfo a).totalSuccessfulDepositsFromL1.val + amount.val < UInt256.size

/-- **A RUN WITH A BACKFILL.**  From fresh storage satisfying `Inv`: `initL2` with the flag set,
the upgrade registration of the base token, then a successful backfill. -/
def Properties.BackfillSatisfiable : Prop :=
  ∃ (cfg : Config) (sl : ChainId) (sys₁ sys₂ sys₃ : Sys) (amount : UInt256),
    Inv cfg (Sys.fresh sl) ∧ amount ≠ 0 ∧
    exec cfg (Sys.fresh sl) (.initL2 true) = some sys₁ ∧
    exec cfg sys₁ .registerBaseDuringUpgrade = some sys₂ ∧
    exec cfg sys₂ (.backfill amount) = some sys₃

end Contracts.L2AssetTracker
