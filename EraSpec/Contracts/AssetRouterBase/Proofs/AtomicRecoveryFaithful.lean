import EraSpec.Contracts.AssetRouterBase.Properties.AtomicRecoveryFaithful
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery

/-!
# Proofs: the router-produced call by destination, and the stranded L2→L1 atomic leg

`routerCallTo` agrees with `AtomicRecovery.routerCall` off L1 (`routerCallTo_of_ne`), so the L2
results are the `AtomicRecovery` certificates after one rewrite.  On L1, the call's target is not
the router, so `recoverCall` takes its `other` branch (`recoverCall_l1`), and the loop results are
`AtomicRecovery.recoverBundle_eq_none_of_blocking` with the trivial invariant.  The send side is a
decision on five conjuncts; for an L1 destination its atomic conjunct follows from the L1 one
(`pinChecks_l1_iff`).
-/

namespace Contracts.AssetRouter.AtomicRecoveryFaithful

open Contracts.AssetRouter.AtomicRecovery
open AttackVectors.RecoveryLimits (Outcome LegState)

variable {X : Type}

/-! ## The call by destination -/

theorem destinationRouter_of_ne {cfg : FConfig} {dest : Chain} (h : dest ≠ cfg.l1Chain) :
    destinationRouter cfg dest = cfg.base.router := by
  unfold destinationRouter
  rw [ite_eq_right h]

theorem destinationRouter_l1 (cfg : FConfig) : destinationRouter cfg cfg.l1Chain = cfg.l1Router := by
  unfold destinationRouter
  rw [ite_eq_left rfl]

theorem routerCallTo_of_ne {cfg : FConfig} {dest : Chain} (h : dest ≠ cfg.l1Chain) (a : AssetId)
    (md : MintData) : routerCallTo cfg dest a md = routerCall cfg.base a md := by
  unfold routerCallTo routerCall
  rw [destinationRouter_of_ne h]

theorem routerCallTo_l1 (cfg : FConfig) (a : AssetId) (md : MintData) :
    routerCallTo cfg cfg.l1Chain a md = { routerCall cfg.base a md with target := cfg.l1Router } := by
  unfold routerCallTo routerCall
  rw [destinationRouter_l1]

/-! ## The refund of an L2→L1 leg -/

/-- The manager's step on the router-produced call to L1 is the `other` branch at the L1 router's
address. -/
theorem recoverCall_l1 {enc : AssetIdOf} {cfg : FConfig} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {w : World X} (hne : cfg.l1Router ≠ cfg.base.router) (a : AssetId) (md : MintData) :
    recoverCall enc cfg.base hk other dest w (routerCallTo cfg cfg.l1Chain a md)
      = other cfg.l1Router w dest (.finalizeDeposit cfg.base.thisChain a (some md)) := by
  rw [routerCallTo_l1]
  unfold recoverCall routerCall
  exact ite_eq_right hne

theorem l1Leg_none {enc : AssetIdOf} {cfg : FConfig} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {w : World X} (hne : cfg.l1Router ≠ cfg.base.router) (hcode : CodelessAt other cfg.l1Router)
    (a : AssetId) (md : MintData) :
    recoverCall enc cfg.base hk other dest w (routerCallTo cfg cfg.l1Chain a md) = none := by
  rw [recoverCall_l1 hne]
  exact hcode _ _ _

theorem l1LegNeverRefunded {enc : AssetIdOf} {cfg : FConfig} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {st : LegState} {w : World X} {calls : List Call} {a : AssetId} {md : MintData}
    (hne : cfg.l1Router ≠ cfg.base.router) (hcode : CodelessAt other cfg.l1Router)
    (hmem : routerCallTo cfg cfg.l1Chain a md ∈ calls) :
    claimRefund (recoverCall enc cfg.base hk other dest) st w calls = none := by
  apply claimRefund_eq_none
  refine recoverBundle_eq_none_of_blocking (fun _ => True)
    (fun c => c = routerCallTo cfg cfg.l1Chain a md) calls w ?_ ?_ ⟨_, hmem, rfl⟩ trivial
  · intro _ _ _ _ _ _ _
    trivial
  · rintro c _ rfl u _
    exact l1Leg_none hne hcode a md

theorem l1LegClaim_iff {enc : AssetIdOf} {cfg : FConfig} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {w w' : World X} {st' : LegState} (hne : cfg.l1Router ≠ cfg.base.router) (a : AssetId)
    (md : MintData) :
    claimRefund (recoverCall enc cfg.base hk other dest) LegState.Revertable w
        [routerCallTo cfg cfg.l1Chain a md] = some (st', w')
      ↔ st' = LegState.Reverted
        ∧ other cfg.l1Router w dest (.finalizeDeposit cfg.base.thisChain a (some md))
            = some (w', true) := by
  unfold claimRefund
  rw [ite_eq_right (fun h => h rfl)]
  unfold recoverBundle
  rw [recoverCall_l1 hne]
  rcases h : other cfg.l1Router w dest (.finalizeDeposit cfg.base.thisChain a (some md))
    with _ | ⟨w₁, b⟩
  · simp
  · cases b
    · simp [recoverBundle]
    · simp only [recoverBundle, ite_true, Nat.add_zero, one_ne_zero, ite_false,
        Option.some.injEq, Prod.mk.injEq, and_true]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩

/-! ## The send side -/

theorem pinSend_of_checks {env : CenterEnv} {dest : Chain} {starters : List Starter}
    {isAtomic : Bool} (h : PinSendChecks env dest starters isAtomic) :
    pinSend env dest starters isAtomic = some (dispatchOf isAtomic) := by
  unfold pinSend
  rw [ite_eq_left h]

theorem pinSend_of_not_checks {env : CenterEnv} {dest : Chain} {starters : List Starter}
    {isAtomic : Bool} (h : ¬ PinSendChecks env dest starters isAtomic) :
    pinSend env dest starters isAtomic = none := by
  unfold pinSend
  rw [ite_eq_right h]

/-- For an L1 destination the atomic conjunct follows from the L1 conjunct. -/
theorem pinChecks_l1_iff (env : CenterEnv) (starters : List Starter) :
    PinSendChecks env env.l1Chain starters true ↔ PinSendChecks env env.l1Chain starters false := by
  unfold PinSendChecks
  constructor
  · rintro ⟨h1, h2, h3, h4, -⟩
    exact ⟨h1, h2, h3, h4, fun h => absurd h (by decide)⟩
  · rintro ⟨h1, h2, h3, h4, -⟩
    exact ⟨h1, h2, h3, h4, fun _ s hs => (h4 rfl s hs).2.2⟩

theorem pinChecks_routerStarter_l1 {env : CenterEnv} (h : env.l1Chain ≠ env.thisChain)
    (isAtomic : Bool) : PinSendChecks env env.l1Chain [routerStarter env] isAtomic := by
  refine ⟨h, h, fun _ => rfl, ?_, ?_⟩
  · intro _ s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact ⟨rfl, rfl, rfl⟩
  · intro _ s hs
    rw [List.mem_singleton] at hs
    subst hs
    rfl

theorem upgradeGuard_rejects_atomic_l1 (env : CenterEnv) :
    ¬ UpgradeAtomicityGuard env env.l1Chain true :=
  fun h => h.1 rfl rfl

/-! ## Certificates -/

theorem RouterCallToL2IsModelled : Properties.RouterCallToL2IsModelled :=
  fun _ _ a md h => routerCallTo_of_ne h a md

theorem RouterCallToL1RetargetsModelled : Properties.RouterCallToL1RetargetsModelled :=
  fun cfg a md => routerCallTo_l1 cfg a md

theorem L1LegRefundBypassesRouter : Properties.L1LegRefundBypassesRouter :=
  fun _ _ _ _ _ _ _ a md hne => recoverCall_l1 hne a md

theorem L1LegRefundReverts : Properties.L1LegRefundReverts := by
  intro X enc cfg hk other dest w a md hne hcode
  rw [l1Leg_none hne hcode a md]
  exact ⟨rfl, rfl⟩

theorem L1LegClaimOnlyByForeignCode : Properties.L1LegClaimOnlyByForeignCode :=
  fun _ _ _ _ _ _ _ _ _ a md hne => l1LegClaim_iff hne a md

theorem L1LegNeverRefunded : Properties.L1LegNeverRefunded :=
  fun _ _ _ _ _ _ _ _ _ _ _ hne hcode hmem => l1LegNeverRefunded hne hcode hmem

theorem PreparedBurnRefundsDepositorToL2 : Properties.PreparedBurnRefundsDepositorToL2 := by
  intro Acc prepHooks s r out hw hprep X enc cfg hk other dest w x₁ hd hp hn ht hf
  rw [routerCallTo_of_ne hd]
  exact Contracts.AssetRouter.AtomicRecovery.PreparedBurnRefundsDepositor Acc prepHooks s r out hw
    hprep X enc cfg.base hk other dest w x₁ hp hn ht hf

theorem PreparedBurnRefundByDestination : Properties.PreparedBurnRefundByDestination := by
  intro Acc prepHooks s r out hw hprep X enc cfg hk other dest w x₁ hne hp hn ht hf
  by_cases hd : dest = cfg.l1Chain
  · rw [ite_eq_left hd]
    subst hd
    exact recoverCall_l1 hne r.assetId out.data
  · rw [ite_eq_right hd]
    exact PreparedBurnRefundsDepositorToL2 Acc prepHooks s r out hw hprep X enc cfg hk other dest w
      x₁ hd hp hn ht hf

theorem PinAdmitsAtomicL1Leg : Properties.PinAdmitsAtomicL1Leg := fun _ h =>
  ⟨pinSend_of_checks (pinChecks_routerStarter_l1 h true),
    pinSend_of_checks (pinChecks_routerStarter_l1 h false)⟩

theorem PinAtomicityIrrelevantToL1 : Properties.PinAtomicityIrrelevantToL1 := by
  intro env starters
  by_cases hc : PinSendChecks env env.l1Chain starters false
  · rw [pinSend_of_checks hc, pinSend_of_checks ((pinChecks_l1_iff env starters).mpr hc)]
    rfl
  · rw [pinSend_of_not_checks hc,
      pinSend_of_not_checks (fun h => hc ((pinChecks_l1_iff env starters).mp h))]
    rfl

theorem UpgradeGuardRejectsAtomicL1 : Properties.UpgradeGuardRejectsAtomicL1 := fun env =>
  ⟨upgradeGuard_rejects_atomic_l1 env, ⟨fun h => absurd h (by decide), fun _ => rfl⟩,
    fun _ hd => ⟨fun _ => hd, fun h => absurd h (by decide)⟩⟩

/-! ## Concrete instances

The router of `AtomicRecovery`'s witnesses (`wCfg`: chain `7`, router `3`, vault `4`, manager `5`)
with `L1_CHAIN_ID = 1` and `L1_ASSET_ROUTER = 13`; the center on chain `7` agrees.  The burn is
`NativeTokenVaultBase.witnessRequest` (one unit of `11`'s balance, remote receiver `12`) sent to a
chosen destination.  Address `13` has no code; every other non-router target declines. -/

def fCfg : FConfig := ⟨wCfg, 1, 13⟩

def fEnv : CenterEnv := ⟨7, 1, 3⟩

/-- Non-router targets: the L1 router's address `13` has no code and reverts; any other target
returns `false` and changes nothing. -/
def codelessOther {X : Type} : Address → World X → Chain → CallData → Option (World X × Bool) :=
  fun t w _ _ => if t = 13 then none else some (w, false)

/-- Every target returns `true` and changes nothing. -/
def trueOther {X : Type} : Address → World X → Chain → CallData → Option (World X × Bool) :=
  fun _ w _ _ => some (w, true)

theorem codelessOther_at : CodelessAt (codelessOther (X := X)) fCfg.l1Router := by
  intro w dest d
  show (if (13 : Address) = 13 then none else some (w, false)) = none
  rw [ite_eq_left rfl]

theorem fCfg_l1Router_ne : fCfg.l1Router ≠ fCfg.base.router := by
  show (13 : Address) ≠ 3
  decide

/-- `NativeTokenVaultBase.witnessRequest`, sent to `dest`. -/
def burnTo (dest : UInt256) : NativeTokenVaultBase.Request :=
  { NativeTokenVaultBase.witnessRequest with destinationChain := dest }

theorem witnessPrep_wellFormed :
    NativeTokenVaultBase.WellFormed NativeTokenVaultBase.witnessPrepState :=
  ⟨NativeTokenVaultBase.witnessToken_ledger, NativeTokenVaultBase.witnessPrep_rc⟩

/-- The witness burn prepares, whatever its destination. -/
theorem burnTo_prepares (dest : UInt256) :
    ∃ out, NativeTokenVaultBase.prepare NativeTokenVaultBase.witnessPrepHooks
      NativeTokenVaultBase.witnessPrepState (burnTo dest) = some out := by
  have htok : NativeTokenVaultBase.witnessPrepState.registry.tokenForAsset (2 + 1) = 5 :=
    NativeTokenVaultBase.witnessPrep_token
  have hs : NativeTokenVaultBase.InScope NativeTokenVaultBase.witnessPrepState (burnTo dest) := by
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    show (if (0 : NativeTokenVaultBase.Address) = 0 then
      NativeTokenVaultBase.witnessPrepState.registry.tokenForAsset (2 + 1) else 0) = 5
    rw [ite_eq_left rfl, htok]
  have hsel : NativeTokenVaultBase.selectedToken NativeTokenVaultBase.witnessPrepState
      (burnTo dest) = 5 := hs.2.2.2.2
  have he : NativeTokenVaultBase.EntryAllowed NativeTokenVaultBase.witnessPrepState
      (burnTo dest) := by
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · rw [hsel]; decide
    · rw [hsel]; exact NativeTokenVaultBase.witnessPrep_asset
    · show (1 : UInt256) ≠ 0
      decide
  have hb : (burnTo dest).data.amount.val ≤
      NativeTokenVaultBase.witnessPrepState.token.balances 11 := by
    show (1 : UInt256).val ≤ Function.update (fun _ => 0) (11 : NativeTokenVaultBase.Address)
      (0 + (1 : UInt256).val) 11
    rw [Function.update_self]
    decide
  have hd : (burnTo dest).depositor ≠ 0 := by
    show (11 : NativeTokenVaultBase.Address) ≠ 0
    decide
  exact NativeTokenVaultBase.preparation_enabled (hooks := NativeTokenVaultBase.witnessPrepHooks)
    (accounted := ()) (metadata := []) witnessPrep_wellFormed hs he rfl hd hb (by decide)
    (by decide) rfl rfl

/-- `AtomicRecovery`'s refund world for the burned asset `2 + 1`: bridged, local token `6`,
origin chain `1`. -/
def fWorld : World Unit := ⟨wRouter, pVault, false, ()⟩

theorem fWorld_known : fWorld.vault.originChain (2 + 1) ≠ wCfg.thisChain ∧
    fWorld.vault.token (2 + 1) ≠ 0 := by
  have ho : pVault.originChain (2 + 1) = 1 := NativeTokenVault.sn_originChain_self _ _ _ _ _
  have htk : pVault.token (2 + 1) = 6 := NativeTokenVault.sn_token_self _ _ _ _ _
  refine ⟨?_, ?_⟩
  · show pVault.originChain (2 + 1) ≠ 7
    rw [ho]; decide
  · show pVault.token (2 + 1) ≠ 0
    rw [htk]; decide

theorem PreparedBurnRefundFailsToL1 : Properties.PreparedBurnRefundFailsToL1 := by
  obtain ⟨out, hout⟩ := burnTo_prepares 1
  have hdest : (burnTo 1).destinationChain = fCfg.l1Chain := rfl
  refine ⟨Unit, NativeTokenVaultBase.witnessPrepHooks, NativeTokenVaultBase.witnessPrepState,
    burnTo 1, out, Unit, wEnc, fCfg, okHooks, codelessOther, fWorld, (), (), witnessPrep_wellFormed,
    hout, hdest, fCfg_l1Router_ne, codelessOther_at, rfl, fWorld_known.1, fWorld_known.2, rfl, rfl,
    ?_, ?_⟩
  · rw [Contracts.AssetRouter.AtomicRecovery.PreparedBurnRefundsDepositor Unit
      NativeTokenVaultBase.witnessPrepHooks NativeTokenVaultBase.witnessPrepState (burnTo 1) out
      witnessPrep_wellFormed hout Unit wEnc fCfg.base okHooks codelessOther
      (burnTo 1).destinationChain fWorld () rfl fWorld_known.1 fWorld_known.2 rfl]
    rfl
  · rw [hdest]
    exact l1Leg_none fCfg_l1Router_ne codelessOther_at _ _

theorem AtomicL1LegIsStranded : Properties.AtomicL1LegIsStranded := by
  obtain ⟨out, hout⟩ := burnTo_prepares 1
  obtain ⟨-, hbal, -, hamt⟩ := NativeTokenVaultBase.preparation_backed witnessPrep_wellFormed hout
  have hdest : (burnTo 1).destinationChain = fCfg.l1Chain := rfl
  have henv : fEnv.l1Chain ≠ fEnv.thisChain := by
    show (1 : Chain) ≠ 7
    decide
  refine ⟨Unit, NativeTokenVaultBase.witnessPrepHooks, NativeTokenVaultBase.witnessPrepState,
    burnTo 1, out, Unit, wEnc, fCfg, fEnv, okHooks, codelessOther, witnessPrep_wellFormed, hout,
    hbal, hamt, hdest, rfl, rfl, rfl, fCfg_l1Router_ne, codelessOther_at,
    (PinAdmitsAtomicL1Leg fEnv henv).1, ?_, upgradeGuard_rejects_atomic_l1 fEnv, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    rfl
  · intro st w
    rw [hdest]
    exact l1LegNeverRefunded fCfg_l1Router_ne codelessOther_at List.mem_cons_self

theorem CustomHandlerBundleIsStrandedToL2 : Properties.CustomHandlerBundleIsStrandedToL2 := by
  have hd : (8 : Chain) ≠ fCfg.l1Chain := by
    show (8 : Chain) ≠ 1
    decide
  have hchecks : PinSendChecks fEnv 8 [routerStarter fEnv, routerStarter fEnv] true := by
    refine ⟨by decide, by decide, fun h => absurd h (by decide), fun h => absurd h (by decide), ?_⟩
    intro _ s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · rfl
    · rw [List.mem_singleton] at hs
      subst hs
      rfl
  refine ⟨Unit, wEnc, fCfg, fEnv, okHooks, declineOther, 8, wWorld, 2, 1, wMd, wMd, hd, rfl, rfl,
    rfl, pinSend_of_checks hchecks, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    · rw [List.mem_singleton] at hc
      subst hc
      rfl
  · show (if wRouter.handler 2 = 0 then (4 : Address) else wRouter.handler 2) ≠ 4
    unfold wRouter; decide
  · show (if wRouter.handler 1 = 0 then (4 : Address) else wRouter.handler 1) = 4
    unfold wRouter; decide
  · rw [routerCallTo_of_ne hd]
    show (claimRefund (recoverCall wEnc wCfg okHooks declineOther 8) LegState.Revertable wWorld
      [routerCall wCfg 1 wMd]).isSome
    rw [wVaultCall_refunded]
    rfl
  · intro w' hr
    rw [routerCallTo_of_ne hd, routerCallTo_of_ne hd]
    exact LegNeverRefunded Unit wEnc wCfg okHooks declineOther 8 wWorld w' _ 2 wVault_unaware_two
      (declineOther_leaves 2) wBundleHas wBundleFails hr

theorem L1LegForeignTrueClosesWithoutRefund : Properties.L1LegForeignTrueClosesWithoutRefund :=
  ⟨Unit, wEnc, fCfg, okHooks, trueOther, 1, wWorld, 1, wMd, fCfg_l1Router_ne,
    (l1LegClaim_iff fCfg_l1Router_ne 1 wMd).mpr ⟨rfl, rfl⟩⟩

theorem PreparedBurnRefundToL2Satisfiable : Properties.PreparedBurnRefundToL2Satisfiable := by
  obtain ⟨out, hout⟩ := burnTo_prepares 8
  have hd : (burnTo 8).destinationChain ≠ fCfg.l1Chain := by
    show (8 : Chain) ≠ 1
    decide
  refine ⟨Unit, NativeTokenVaultBase.witnessPrepHooks, NativeTokenVaultBase.witnessPrepState,
    burnTo 8, out, Unit, wEnc, fCfg, okHooks, codelessOther, fWorld, (), witnessPrep_wellFormed,
    hout, by decide, hd, fCfg_l1Router_ne, rfl, fWorld_known.1, fWorld_known.2, rfl, ?_⟩
  rw [PreparedBurnRefundsDepositorToL2 Unit NativeTokenVaultBase.witnessPrepHooks
    NativeTokenVaultBase.witnessPrepState (burnTo 8) out witnessPrep_wellFormed hout Unit wEnc fCfg
    okHooks codelessOther (burnTo 8).destinationChain fWorld () hd rfl fWorld_known.1
    fWorld_known.2 rfl]
  rfl

end Contracts.AssetRouter.AtomicRecoveryFaithful
