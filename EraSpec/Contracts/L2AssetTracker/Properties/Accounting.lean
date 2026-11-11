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
  `E = MAX - snapshot` is `0` for a token registered as new and the vault's balance at
  registration for a legacy one; and `Σin ≤ E + Σout`.
* `InflowOverflowIsCap`: an inbound native transfer succeeds IFF `Σin + amount ≤ E + Σout`.  The
  checked `+=` at `TRK:296` reverts on everything else, so the chain balance blocks every release
  beyond what went out.  This contradicts the NatSpec at `TRK:39-41` ("write-only bookkeeping
  ... not consulted by any bridging decision"); `ChainBalanceGatesInflow` is a concrete run.
* `OutflowIffNetOutFits`: an outbound native transfer succeeds IFF the net amount out, this one
  included, still fits in a `uint256` (`E + Σout + amount ≤ MAX + Σin`).  Since that net amount
  is escrowed in the vault (`_depositFunds` runs right after the hook), it is at most the token's
  total supply, so for a token with supply below `2^256` the outflow never reverts on the
  chain balance.
* `TokenReadsIgnoredOnceRegistered`: after registration the tracker never reads the token, so a
  direct transfer into the vault never moves the chain balance or the cap afterwards; one made
  before a legacy first touch is counted in `E` as if bridged out (`TRK:325-326`).

## The round trip

* `TrackerHooksCancelOffL1`: an outbound transfer (vault hook, `TRK:221-250`) followed by an
  inbound one of the same chain, asset and amount (`TRK:269-305`) restores the storage exactly,
  up to the first-touch registration of the asset, when the chain is not L1 or the chain settles
  off L1 at both calls.  That is the law `NativeTokenVaultBase.HooksCancelModulo` the vault's
  round trip needs on L2.
* `L1CountersMoveTogether`: when the chain is L1 and the chain settles on L1 at both calls, the
  same round trip raises BOTH `totalWithdrawalsToL1` and `totalSuccessfulDepositsFromL1` by the
  amount: neither is restored.

## The base token

* `BaseFinalizeNeverCreditsChainBalance`: `handleFinalizeBaseTokenBridgingOnL2` never changes
  the chain balance of a registered base token, native or not (`TRK:377` hard-codes
  `_isNativeToThisChain: false`); the outbound base path debits it when the base token is native
  here (`TRK:256-260`).
* `BaseTokenNativeAsymmetry` (countermodel): with a base token native to this chain, an outbound
  and an inbound base transfer of the same amount leave the chain balance lowered by the amount,
  and the sentinel fails.  The premise `BaseNotSelfNative` of `Inv` is therefore load-bearing.
  At UPG `assertRecoveryIsAccountingNeutral` reverts for exactly this configuration
  (`BaseTokenNativeToThisChain`, `UPG/bridge/asset-tracker/L2AssetTracker.sol:182-184`).

## Registration and the backfill

* `RegistrationMonotone`: a registered asset stays registered, and its snapshot never changes
  except by the backfill of the base token.
* `BackfillOnlyBaseFromZero`: a backfill writes only the base token's snapshot, from a saved
  zero, and clears its flag.
* `BackfillAtMostOnce`: after one backfill no later one succeeds, on any run from a state
  satisfying `Inv`.

## Non-vacuity

`AccountingRunSatisfiable` is a run from fresh storage in which a native asset registered as new
and a legacy native asset (with `E ≠ 0`) both have nonzero flows; it meets the premises of
`NativeSentinel`, `InflowOverflowIsCap` and `OutflowIffNetOutFits`, with an inbound amount
accepted and a larger one rejected.  `TrackerRoundTripSatisfiable` meets the premises of
`TrackerHooksCancelOffL1` on an unregistered legacy asset (so the registration is not the
identity) and of `L1CountersMoveTogether`.  `BackfillSatisfiable` is a run with a successful
backfill.  The countermodels are their own witnesses.
-/

namespace Contracts.L2AssetTracker

/-! ## The invariant -/

/-- **THE INVARIANT HOLDS ALONG EVERY RUN.**  From a state satisfying `Inv`, every state reachable
by successful calls (any entry point, by its permitted caller, with any token reads, and any
change of settlement layer) satisfies `Inv`. -/
def Properties.AccountingInvariant : Prop :=
  ∀ (cfg : Config) (sys₀ sys : Sys), Inv cfg sys₀ → Reach cfg sys₀ sys → Inv cfg sys

/-- **THE DEPLOYED STARTING POINT.**  Fresh storage with an empty audit satisfies `Inv`, on any
settlement layer, when neither the base asset the upgrader will install nor the zero asset id
(the base asset id before `initL2`) is native here. -/
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

/-- **ONCE REGISTERED, THE TRACKER NEVER READS THE TOKEN.**  For a registered asset, the vault's
outbound and inbound calls give the same result whatever the token reads are.  So a direct
transfer into the vault after registration (it changes only `balanceOf(vault)`) never moves the
chain balance or the cap; one made before a legacy first touch is counted in `E` as if it had been
bridged out (`TRK:325-326`), and is releasable only against inbound transfers that do not exist. -/
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

/-- **COUNTERMODEL TO "WRITE-ONLY BOOKKEEPING" (`TRK:39-41`).**  From fresh storage, after the
vault registers a native asset as new, an inbound transfer of one unit reverts; after an
outbound transfer of one unit first, the same inbound transfer succeeds.  The two runs differ
only in the chain balance, so the chain balance decides whether the release happens. -/
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
on L1 at both calls, after a successful outbound call, every successful inbound call of the same
chain, asset and amount leaves storage equal to the registration `st₀` except that
`interopInfo[a]` has BOTH counters raised by `amount`; the inbound call fails only if the deposit
counter would overflow. -/
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

/-- **COUNTERMODEL: A BASE TOKEN NATIVE HERE LOSES CHAIN BALANCE ON EVERY ROUND TRIP.**  With a
base token native to this chain (registered as new, so with chain balance `MAX`), an outbound
base transfer of one unit followed by an inbound one of one unit both succeed, off L1, and leave
the chain balance at `MAX - 1`; the sentinel held before and fails after. -/
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
asset stays registered; and across any single step, its snapshot is unchanged unless the step is
the backfill of the base token from a saved zero. -/
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

/-- **THE SENTINEL AND CAP PREMISES ON A NONTRIVIAL RUN.**  From fresh storage (which satisfies
`Inv`), a run that registers native asset `a` as new and native asset `b` as legacy with the
vault holding `E ≠ 0` of it, and moves nonzero amounts of both out and in.  At its end both are
registered and native, `a`'s and `b`'s inbound transfers touch no L1 counter, an inbound transfer
of `b` within the cap succeeds and one beyond it fails. -/
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

/-- **THE ROUND-TRIP PREMISES, WITH A REAL REGISTRATION AND WITH THE L1 COUNTERS.**  An
unregistered legacy asset whose outbound call off L1 succeeds, with a registration that is not the
identity; and a registered asset whose outbound call to L1 while settling on L1 succeeds. -/
def Properties.TrackerRoundTripSatisfiable : Prop :=
  ∃ (cfg : Config) (st st' st₁ st₁' : Storage) (sl : ChainId) (reads : TokenReads)
    (c c' : ChainId) (a : AssetId) (amount : UInt256),
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
