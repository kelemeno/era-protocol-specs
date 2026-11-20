import EraSpec.Contracts.AssetRouterBase.History.Properties.AtomicRecoveryFaithful
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery
import EraSpec.Contracts.AssetRouterBase.History.Proofs.AtomicRecovery

/-!
# Proofs: the router-produced call by destination, and the stranded L2→L1 atomic leg

`routerCallTo` agrees with `AtomicRecovery.routerCall` off L1 (`routerCallTo_of_ne`), so the L2
results are the `AtomicRecovery` certificates after one rewrite.  On L1, the call's target is not
the router, so `recoverCall` takes its `other` branch (`recoverCall_l1`), and the loop results are
`AtomicRecovery.recoverBundle_eq_none_of_blocking` with the trivial invariant.  The send side is a
decision on five conjuncts.  For an L1 destination its atomic conjunct follows from the L1 one
(`pinChecks_l1_iff`), and the L1 conjuncts leave one starter list (`pinChecks_l1_starters`).  The
call formed from the router's starter differs from `routerCallTo` in its sender alone
(`formedCall_routerStarter`), which is where headline (d) uses the agreement on the router's
address.  The concrete headline (d) is headline (d) applied to the witness.
-/

namespace Contracts.AssetRouter.AtomicRecoveryFaithful.History

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

/-- The call the center forms from the router's starter is the router-produced call, when the
center's `L2_ASSET_ROUTER_ADDR` is the router's address. -/
theorem formedCall_routerStarter {cfg : FConfig} {env : CenterEnv}
    (h : env.l2Router = cfg.base.router) (dest : Chain) (a : AssetId) (md : MintData) :
    formedCall cfg dest (routerStarter env) a md = routerCallTo cfg dest a md := by
  show (⟨destinationRouter cfg dest, env.l2Router, 0,
    .finalizeDeposit cfg.base.thisChain a (some md)⟩ : Call) = routerCallTo cfg dest a md
  rw [h]
  rfl

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

/-- For an L1 destination the checks leave exactly one starter list. -/
theorem pinChecks_l1_starters {env : CenterEnv} {starters : List Starter} {isAtomic : Bool}
    (h : PinSendChecks env env.l1Chain starters isAtomic) : starters = [routerStarter env] := by
  obtain ⟨-, -, hlen, hcall, -⟩ := h
  obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp (hlen rfl)
  obtain ⟨hi, hr, hv⟩ := hcall rfl s List.mem_cons_self
  obtain ⟨rc, ind, v⟩ := s
  dsimp only at hi hr hv
  subst hi hr hv
  rfl

theorem upgradeGuard_rejects_atomic_l1 (env : CenterEnv) :
    ¬ UpgradeAtomicityGuard env env.l1Chain true :=
  fun h => h.1 rfl rfl

/-! ## Certificates -/

theorem RouterCallToL2IsModelled : Properties.RouterCallToL2IsModelled :=
  fun _ _ a md h => routerCallTo_of_ne h a md

theorem RouterCallToL1RetargetsModelled : Properties.RouterCallToL1RetargetsModelled :=
  fun cfg a md => routerCallTo_l1 cfg a md

theorem RouterStarterFormsRouterCall : Properties.RouterStarterFormsRouterCall :=
  fun _ _ dest a md =>
    ⟨fun h => congrArg Call.sender h, fun h => formedCall_routerStarter h dest a md⟩

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
  exact Contracts.AssetRouter.AtomicRecovery.History.PreparedBurnRefundsDepositor Acc prepHooks s r out hw
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

theorem PinL1SendIsRouterStarter : Properties.PinL1SendIsRouterStarter := by
  intro env starters isAtomic d h
  by_cases hc : PinSendChecks env env.l1Chain starters isAtomic
  · exact pinChecks_l1_starters hc
  · rw [pinSend_of_not_checks hc] at h
    cases h

theorem UpgradeGuardRejectsAtomicL1 : Properties.UpgradeGuardRejectsAtomicL1 := fun env =>
  ⟨upgradeGuard_rejects_atomic_l1 env, ⟨fun h => absurd h (by decide), fun _ => rfl⟩,
    fun _ hd => ⟨fun _ => hd, fun h => absurd h (by decide)⟩⟩

theorem AdmittedAtomicL1LegNeverRefunded : Properties.AdmittedAtomicL1LegNeverRefunded := by
  intro X enc cfg env hk other a md hL2 hl1 hr hne hcode
  have hcall : formedCall cfg env.l1Chain (routerStarter env) a md
      = routerCallTo cfg cfg.l1Chain a md := by
    rw [formedCall_routerStarter hr, hl1]
  refine ⟨(PinAdmitsAtomicL1Leg env hL2).1, hcall, ?_, upgradeGuard_rejects_atomic_l1 env, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    rfl
  · intro st w
    rw [hcall]
    exact l1LegNeverRefunded hne hcode List.mem_cons_self

/-! ## Concrete instances

One chain, `7`, with `AtomicRecovery`'s addresses (`wCfg`: router `3`, vault `4`, manager `5`),
`L1_CHAIN_ID = 1` and `L1_ASSET_ROUTER = 13`; the center on chain `7` agrees.  The burned asset
`2 + 1` is bridged from chain `1`, with origin token `9` and local token `6`, in the burning
vault's state (`fPrepState`) and in the refund world's registry (`fWorld`) alike.  The burn
(`fBurn`) is called by router `3` on vault `4`: one unit of `11`'s balance, remote receiver `12`,
to a chosen destination.  Its mint data is `AtomicRecovery`'s `wMd` (`fBurn_data`).  Address `13`
has no code; every other non-router target declines. -/

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

theorem fEnv_l2 : fEnv.l1Chain ≠ fEnv.thisChain := by
  show (1 : Chain) ≠ 7
  decide

/-- The ledger of the bridged token at `6`: its vault is `4`, its origin token `9`, and `11`
holds one unit. -/
def fToken : BridgedStandardERC20.State :=
  BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty ⟨4, 9, 2 + 1⟩) 11 1

theorem fToken_ledger : BridgedStandardERC20.WellFormed fToken := by
  have hempty : BridgedStandardERC20.WellFormed (BridgedStandardERC20.empty ⟨4, 9, 2 + 1⟩) := by
    refine ⟨Finset.sum_const_zero, ?_, rfl⟩
    norm_num [BridgedStandardERC20.empty, UInt256.size]
  have hmint : BridgedStandardERC20.mint (BridgedStandardERC20.empty ⟨4, 9, 2 + 1⟩) 4 11 1
      = some fToken := by
    unfold BridgedStandardERC20.mint
    rw [ite_eq_left]
    · rfl
    · refine ⟨by decide, rfl, by decide, ?_⟩
      norm_num [BridgedStandardERC20.empty, UInt256.size]
  exact BridgedStandardERC20.mint_preserves_ledger hempty hmint

/-- The vault's two registry maps: asset `2 + 1` and token `6` name each other. -/
def fRegistry : NativeTokenVaultBase.Registry :=
  ⟨Function.update (fun _ : UInt256 => (0 : NativeTokenVaultBase.Address)) (2 + 1) 6,
    Function.update (fun _ : NativeTokenVaultBase.Address => (0 : UInt256)) 6 (2 + 1)⟩

theorem fRegistry_token : fRegistry.tokenForAsset (2 + 1) = 6 := by
  show Function.update (fun _ : UInt256 => (0 : NativeTokenVaultBase.Address)) (2 + 1) 6 (2 + 1) = 6
  exact Function.update_self _ _ _

theorem fRegistry_asset : fRegistry.assetForToken 6 = 2 + 1 := by
  show Function.update (fun _ : NativeTokenVaultBase.Address => (0 : UInt256)) 6 (2 + 1) 6 = 2 + 1
  exact Function.update_self _ _ _

/-- The burning vault, in the vault-preparation model: vault `4` with asset router `3`, on chain
`7`, tracking token `6` for asset `2 + 1`, which is bridged from chain `1`.  Base asset `0`. -/
def fPrepState : NativeTokenVaultBase.State Unit :=
  ⟨⟨4, 3, 6, 2 + 1, 0, 7, 1⟩, fRegistry, false, fToken, ()⟩

theorem fPrep_wellFormed : NativeTokenVaultBase.WellFormed fPrepState :=
  ⟨fToken_ledger, rfl, rfl, fRegistry_token, fRegistry_asset⟩

/-- A burn of one unit of `11`'s balance of asset `2 + 1` towards `dest`, with remote receiver
`12`, called by router `3`.  The token is resolved from the registry (zero hint). -/
def fBurn (dest : UInt256) : NativeTokenVaultBase.Request :=
  ⟨3, dest, 2 + 1, 11, 0, 0, ⟨1, 12, 0⟩⟩

/-- The witness burn prepares, whatever its destination. -/
theorem fBurn_prepares (dest : UInt256) :
    ∃ out, NativeTokenVaultBase.prepare NativeTokenVaultBase.witnessPrepHooks fPrepState
      (fBurn dest) = some out := by
  have hs : NativeTokenVaultBase.InScope fPrepState (fBurn dest) := by
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    show (if (0 : NativeTokenVaultBase.Address) = 0 then
      fPrepState.registry.tokenForAsset (2 + 1) else 0) = 6
    rw [ite_eq_left rfl]
    exact fRegistry_token
  have hsel : NativeTokenVaultBase.selectedToken fPrepState (fBurn dest) = 6 := hs.2.2.2.2
  have he : NativeTokenVaultBase.EntryAllowed fPrepState (fBurn dest) := by
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · rw [hsel]; decide
    · rw [hsel]; exact fRegistry_asset
    · show (1 : UInt256) ≠ 0
      decide
  have hb : (fBurn dest).data.amount.val ≤ fPrepState.token.balances 11 := by
    show (1 : UInt256).val ≤ Function.update (fun _ => 0) (11 : NativeTokenVaultBase.Address)
      (0 + (1 : UInt256).val) 11
    rw [Function.update_self]
    decide
  have hd : (fBurn dest).depositor ≠ 0 := by
    show (11 : NativeTokenVaultBase.Address) ≠ 0
    decide
  exact NativeTokenVaultBase.preparation_enabled (hooks := NativeTokenVaultBase.witnessPrepHooks)
    (accounted := ()) (metadata := []) fPrep_wellFormed hs he rfl hd hb (by decide)
    (by decide) rfl rfl

/-- The burn's mint data is `AtomicRecovery`'s `wMd`: original caller `11`, remote receiver `12`,
origin token `9`, amount `1`, empty metadata. -/
theorem fBurn_data {dest : UInt256} {out : NativeTokenVaultBase.Result Unit}
    (h : NativeTokenVaultBase.prepare NativeTokenVaultBase.witnessPrepHooks fPrepState (fBurn dest)
      = some out) : out.data = wMd := by
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := NativeTokenVaultBase.preparation_payload fPrep_wellFormed h
  have hm : out.data.metadata = [] := (Option.some.inj h6).symm
  rcases hdata : out.data with ⟨oc, rr, ot, amt, md⟩
  rw [hdata] at h1 h2 h3 h4 hm
  dsimp only at h1 h2 h3 h4 hm
  subst h1 h2 h3 h4 hm
  rfl

/-- The burning vault is `fCfg`'s vault, on its chain, with its router, and the burn is called by
that router. -/
theorem fBurn_on_fCfg (dest : UInt256) :
    fPrepState.config.chainId = fCfg.base.thisChain
    ∧ NativeTokenVaultBase.widen fPrepState.config.vault = fCfg.base.ntv
    ∧ NativeTokenVaultBase.widen fPrepState.config.router = fCfg.base.router
    ∧ NativeTokenVaultBase.widen (fBurn dest).caller = fCfg.base.router := by
  refine ⟨rfl, by decide, by decide, ?_⟩
  show NativeTokenVaultBase.widen (3 : NativeTokenVaultBase.Address) = (3 : Address)
  decide

/-- `AtomicRecovery`'s refund world for the burned asset `2 + 1`: bridged, local token `6`,
origin token `9`, origin chain `1`. -/
def fWorld : World Unit := ⟨wRouter, pVault, false, ()⟩

theorem fWorld_token : fWorld.vault.token (2 + 1) = 6 := NativeTokenVault.sn_token_self _ _ _ _ _

theorem fWorld_origin : fWorld.vault.originChain (2 + 1) = 1 :=
  NativeTokenVault.sn_originChain_self _ _ _ _ _

theorem fWorld_known : fWorld.vault.originChain (2 + 1) ≠ wCfg.thisChain ∧
    fWorld.vault.token (2 + 1) ≠ 0 := by
  rw [fWorld_origin, fWorld_token]
  decide

/-- The refund world's registry has the burned asset's local token and origin chain as the
burning vault has them. -/
theorem fWorld_same_asset (dest : UInt256) :
    fWorld.vault.token (fBurn dest).assetId
        = NativeTokenVaultBase.widen fPrepState.config.tokenAddress
    ∧ fWorld.vault.originChain (fBurn dest).assetId = fPrepState.config.originChainId := by
  refine ⟨?_, ?_⟩
  · show fWorld.vault.token (2 + 1) = NativeTokenVaultBase.widen 6
    rw [fWorld_token]
    decide
  · exact fWorld_origin

theorem PreparedBurnRefundFailsToL1 : Properties.PreparedBurnRefundFailsToL1 := by
  obtain ⟨out, hout⟩ := fBurn_prepares 1
  obtain ⟨hchain, hvault, hrouter, hcaller⟩ := fBurn_on_fCfg 1
  have hdest : (fBurn 1).destinationChain = fCfg.l1Chain := rfl
  have hother : (fBurn 1).destinationChain ≠ fCfg.base.thisChain := by
    show (1 : Chain) ≠ 7
    decide
  refine ⟨Unit, NativeTokenVaultBase.witnessPrepHooks, fPrepState, fBurn 1, out, Unit, wEnc, fCfg,
    okHooks, codelessOther, fWorld, (), (), fPrep_wellFormed, hout, hchain, hvault, hrouter,
    hcaller, (fWorld_same_asset 1).1, (fWorld_same_asset 1).2, hother, hdest, fCfg_l1Router_ne,
    codelessOther_at, rfl, fWorld_known.1, fWorld_known.2, rfl, rfl, ?_, ?_⟩
  · rw [Contracts.AssetRouter.AtomicRecovery.History.PreparedBurnRefundsDepositor Unit
      NativeTokenVaultBase.witnessPrepHooks fPrepState (fBurn 1) out fPrep_wellFormed hout Unit wEnc
      fCfg.base okHooks codelessOther (fBurn 1).destinationChain fWorld () rfl fWorld_known.1
      fWorld_known.2 rfl]
    rfl
  · rw [hdest]
    exact l1Leg_none fCfg_l1Router_ne codelessOther_at _ _

theorem AtomicL1LegIsStranded : Properties.AtomicL1LegIsStranded := by
  obtain ⟨out, hout⟩ := fBurn_prepares 1
  obtain ⟨-, hbal, -, hamt⟩ := NativeTokenVaultBase.preparation_backed fPrep_wellFormed hout
  obtain ⟨hchain, hvault, hrouter, hcaller⟩ := fBurn_on_fCfg 1
  -- headline (d), on the witness's center, router and environment, for the burn's mint data
  obtain ⟨hsend, hcall, hvalid, hguard, hclaim⟩ := AdmittedAtomicL1LegNeverRefunded Unit wEnc fCfg
    fEnv okHooks codelessOther (fBurn 1).assetId out.data fEnv_l2 rfl rfl fCfg_l1Router_ne
    codelessOther_at
  exact ⟨Unit, NativeTokenVaultBase.witnessPrepHooks, fPrepState, fBurn 1, out, Unit, wEnc, fCfg,
    fEnv, okHooks, codelessOther, fPrep_wellFormed, hout, hbal, hamt, hchain, hvault, hrouter,
    hcaller, rfl, rfl, rfl, rfl, fCfg_l1Router_ne, codelessOther_at, hsend, hcall, hvalid, hguard,
    hclaim⟩

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
  have hr : fEnv.l2Router = fCfg.base.router := rfl
  refine ⟨Unit, wEnc, fCfg, fEnv, okHooks, declineOther, 8, wWorld, 2, 1, wMd, wMd, hd, rfl, rfl,
    hr, pinSend_of_checks hchecks, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [formedCall_routerStarter hr, formedCall_routerStarter hr]
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
    rw [AtomicRecovery.History.wVaultCall_refunded]
    rfl
  · intro w' hr
    rw [routerCallTo_of_ne hd, routerCallTo_of_ne hd]
    exact AtomicRecovery.History.LegNeverRefunded Unit wEnc wCfg okHooks declineOther 8 wWorld w' _ 2 wVault_unaware_two
      (declineOther_leaves 2) wBundleHas wBundleFails hr

theorem L1LegForeignTrueClosesWithoutRefund : Properties.L1LegForeignTrueClosesWithoutRefund :=
  ⟨Unit, wEnc, fCfg, okHooks, trueOther, 1, wWorld, 1, wMd, fCfg_l1Router_ne, rfl, rfl,
    (l1LegClaim_iff fCfg_l1Router_ne 1 wMd).mpr ⟨rfl, rfl⟩⟩

theorem PreparedBurnRefundToL2Satisfiable : Properties.PreparedBurnRefundToL2Satisfiable := by
  obtain ⟨out, hout⟩ := fBurn_prepares 8
  obtain ⟨hchain, hvault, hrouter, hcaller⟩ := fBurn_on_fCfg 8
  have hd : (fBurn 8).destinationChain ≠ fCfg.l1Chain := by
    show (8 : Chain) ≠ 1
    decide
  have hother : (fBurn 8).destinationChain ≠ fCfg.base.thisChain := by
    show (8 : Chain) ≠ 7
    decide
  refine ⟨Unit, NativeTokenVaultBase.witnessPrepHooks, fPrepState, fBurn 8, out, Unit, wEnc, fCfg,
    okHooks, codelessOther, fWorld, (), fPrep_wellFormed, hout, hchain, hvault, hrouter, hcaller,
    (fWorld_same_asset 8).1, (fWorld_same_asset 8).2, by decide, hother, hd, fCfg_l1Router_ne, rfl,
    fWorld_known.1, fWorld_known.2, rfl, ?_⟩
  rw [PreparedBurnRefundsDepositorToL2 Unit NativeTokenVaultBase.witnessPrepHooks fPrepState
    (fBurn 8) out fPrep_wellFormed hout Unit wEnc fCfg okHooks codelessOther
    (fBurn 8).destinationChain fWorld () hd rfl fWorld_known.1 fWorld_known.2 rfl]
  rfl

end Contracts.AssetRouter.AtomicRecoveryFaithful.History
