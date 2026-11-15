import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecoveryFaithful
import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation

/-!
# Properties: the router-produced call by destination, and the stranded L2→L1 atomic leg

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecoveryFaithful`.  Proofs are in
`EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecoveryFaithful`.

`AtomicRecovery` models a router-produced bundle call as `routerCall`, with the L2 router as its
target.  That is the real call only when the destination is another L2.  For an L1 destination
the router targets `L1_ASSET_ROUTER` (`L2AssetRouter.sol:336`).  This file restates the results
that use `routerCall` over the real call, `routerCallTo`, and adds what happens on the L1 branch.

* **To another L2, nothing changes.**  The real call is `routerCall` (`RouterCallToL2IsModelled`).
  Headline (c) holds with the explicit, satisfiable premise that the destination is not L1
  (`PreparedBurnRefundsDepositorToL2`, `PreparedBurnRefundToL2Satisfiable`).  The concrete
  custom-handler stranding holds on a bundle that passes `PinSendChecks`
  (`CustomHandlerBundleIsStrandedToL2`).
* **To L1, the refund bypasses the router.**  The call differs from `routerCall` only in its
  target (`RouterCallToL1RetargetsModelled`).  Its refund is whatever the code at the L1 router's
  address on L2 does (`L1LegRefundBypassesRouter`), and a one-call claim succeeds only if that
  code returns `true` (`L1LegClaimOnlyByForeignCode`).  That code cannot run the vault's refund,
  which is `onlyAssetRouter`.  If it returns `true` and moves nothing, the claim closes the leg
  with nothing refunded (witness: `L1LegForeignTrueClosesWithoutRefund`).  With no code at that
  address, the refund reverts (`L1LegRefundReverts`) and every claim of the bundle reverts
  (`L1LegNeverRefunded`).
* **The original headline (c) is false for an L2→L1 leg.**  One prepared burn to L1 satisfies
  every premise of `AtomicRecovery.Properties.PreparedBurnRefundsDepositor`, and its modelled call
  is refunded, but its real call's refund reverts (`PreparedBurnRefundFailsToL1`).  An exact
  replacement for every destination is the case split `PreparedBurnRefundByDestination`.
* **The pin's modelled checks admit such a leg, and the other tree's guard does not.**  At the
  pin, atomicity never changes whether an L1 send passes `PinSendChecks`.  It only turns
  publication into an `append` (`PinAtomicityIrrelevantToL1`, `PinAdmitsAtomicL1Leg`).  The one
  starter list those checks admit for L1 is the router's (`PinL1SendIsRouterStarter`).  The call
  the center forms from it is the router-produced call exactly when the center's
  `L2_ASSET_ROUTER_ADDR` is the router's (`RouterStarterFormsRouterCall`).  The guard of the other
  tree, `e561b9cc2`, rejects the atomic L1 send and keeps the L1 withdrawal and atomic sends to
  other chains (`UpgradeGuardRejectsAtomicL1`).
* **Headline (d): `AdmittedAtomicL1LegNeverRefunded`.**  Take any L2 whose center and router agree
  on `L1_CHAIN_ID` and `L2_ASSET_ROUTER_ADDR`, under the two environment premises.  The atomic
  one-starter send to L1 passes the modelled checks and is appended instead of published.  No
  claim of the bundle the center forms from it ever succeeds, in any world, whatever the leg's
  state.  `AtomicL1LegIsStranded` is one instance, with a prepared burn that debits the depositor
  behind the bundle's mint data.  Since L1 executes only published bundles (`Specs` header, argued
  from source), the burned amount is then neither minted on L1 nor refunded.

Environment premises: `L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR` (`OPS-CONFIG`) and
`CodelessAt other L1_ASSET_ROUTER` (`VM-CALL`, about that one address).  Both are satisfied by the
witnesses.  No result takes a hash premise.

The three instances with a prepared burn (`PreparedBurnRefundFailsToL1`,
`PreparedBurnRefundToL2Satisfiable`, `AtomicL1LegIsStranded`) tie the burning vault to the
configuration where the send and the refund happen.  The vault's chain id, its own address and
its asset router are the configuration's, the burn's destination is another chain, and the
burn's caller is that router (`bridgeBurn` is
`onlyAssetRouter`, `NativeTokenVaultBase.sol:326`; on L2 that router is `L2_ASSET_ROUTER_ADDR`,
`L2NativeTokenVault.sol:248-250`).  In the two with a refund world, that world's registry has
the burned asset's local token and origin chain as the burning vault has them.  The vault model's
addresses are 160-bit, so they are compared through the zero extension
`NativeTokenVaultBase.widen`.
-/

namespace Contracts.AssetRouter.AtomicRecoveryFaithful

open Contracts.AssetRouter.AtomicRecovery
open AttackVectors.RecoveryLimits (Outcome LegState)

/-! ## The call by destination -/

/-- **TO ANOTHER L2, THE CALL IS `AtomicRecovery`'S.**  For every destination other than the
router's `L1_CHAIN_ID`, the router-produced call is `AtomicRecovery.routerCall`.  So every
`AtomicRecovery` result about `routerCall` is a result about the real call to that destination. -/
def Properties.RouterCallToL2IsModelled : Prop :=
  ∀ (cfg : FConfig) (dest : Chain) (a : AssetId) (md : MintData),
    dest ≠ cfg.l1Chain → routerCallTo cfg dest a md = routerCall cfg.base a md

/-- **TO L1, ONLY THE TARGET DIFFERS.**  The router-produced call to L1 is
`AtomicRecovery.routerCall` with its target replaced by `L1_ASSET_ROUTER`.  Its sender, value and
data are the same (`L2AssetRouter.sol:333-341`). -/
def Properties.RouterCallToL1RetargetsModelled : Prop :=
  ∀ (cfg : FConfig) (a : AssetId) (md : MintData),
    routerCallTo cfg cfg.l1Chain a md = { routerCall cfg.base a md with target := cfg.l1Router }

/-- **THE CENTER FORMS THE ROUTER-PRODUCED CALL FROM THE ROUTER'S STARTER, EXACTLY WHEN THE TWO
AGREE ON THE ROUTER'S ADDRESS.**  For every destination, asset and mint data, the call the center
forms from the router's starter (`formedCall`, `InteropCenter.sol:709-740`) is the router-produced
call `routerCallTo` if and only if the center's `L2_ASSET_ROUTER_ADDR` is the router's address.
The formed call's `from` is the starter's recipient (`:739`), which is the center's
`L2_ASSET_ROUTER_ADDR`.  The "if" direction is what ties the starters `pinSend` admits to the
bundle whose refund the other results describe.  The "only if" direction compares `from` fields
alone: when the two addresses differ, the starter's recipient is some other contract, whose
formed call `formedCall` does not model (`Specs`). -/
def Properties.RouterStarterFormsRouterCall : Prop :=
  ∀ (cfg : FConfig) (env : CenterEnv) (dest : Chain) (a : AssetId) (md : MintData),
    formedCall cfg dest (routerStarter env) a md = routerCallTo cfg dest a md
      ↔ env.l2Router = cfg.base.router

/-! ## The refund of an L2→L1 leg -/

/-- **AN L2→L1 LEG'S REFUND BYPASSES THE ROUTER.**  When `L1_ASSET_ROUTER` is not
`L2_ASSET_ROUTER_ADDR`, the manager's refund of the router-produced call to L1 is exactly what the
code at the L1 router's address on this chain does.  The router's `recoverAtomicCall` is not
called, and so neither is the vault's refund: the result depends on neither the encoding nor the
vault's hooks. -/
def Properties.L1LegRefundBypassesRouter : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (a : AssetId) (md : MintData),
    cfg.l1Router ≠ cfg.base.router →
      recoverCall enc cfg.base hk other dest w (routerCallTo cfg cfg.l1Chain a md)
        = other cfg.l1Router w dest (.finalizeDeposit cfg.base.thisChain a (some md))

/-- **WITH NO CODE AT THE L1 ROUTER'S ADDRESS, THE REFUND REVERTS.**  Its outcome is `reverts`,
the case `AttackVectors.RecoveryLimits` shows blocks the whole claim.  Witness:
`AtomicL1LegIsStranded`. -/
def Properties.L1LegRefundReverts : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (a : AssetId) (md : MintData),
    cfg.l1Router ≠ cfg.base.router → CodelessAt other cfg.l1Router →
      recoverCall enc cfg.base hk other dest w (routerCallTo cfg cfg.l1Chain a md) = none
      ∧ outcomeOf (recoverCall enc cfg.base hk other dest w (routerCallTo cfg cfg.l1Chain a md))
          = Outcome.reverts

/-- **THE ONE-CALL CLAIM SUCCEEDS ONLY IF THAT CODE RETURNS `true`.**  No premise about what is at
the L1 router's address.  A bundle to L1 has exactly one call (`InteropCenter.sol:382-384`).  Its
claim on a `Revertable` leg succeeds exactly when the code at the L1 router's address returns
`true`.  A `false` leaves `recovered == 0` (`AtomicFlowManager.sol:229`).  The claim's resulting
world is that code's. -/
def Properties.L1LegClaimOnlyByForeignCode : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w w' : World X) (st' : LegState) (a : AssetId) (md : MintData),
    cfg.l1Router ≠ cfg.base.router →
      (claimRefund (recoverCall enc cfg.base hk other dest) LegState.Revertable w
          [routerCallTo cfg cfg.l1Chain a md] = some (st', w')
        ↔ st' = LegState.Reverted
          ∧ other cfg.l1Router w dest (.finalizeDeposit cfg.base.thisChain a (some md))
              = some (w', true))

/-- **AN L2→L1 LEG IS NEVER REFUNDED.**  Premises: `L1_ASSET_ROUTER` is not `L2_ASSET_ROUTER_ADDR`,
and the L1 router's address has no code on this chain.  Then every claim of every bundle that
contains the router-produced call to L1 reverts.  This holds for every leg state, every world,
every destination the loop passes, and whatever the other calls do.  Witness:
`AtomicL1LegIsStranded`. -/
def Properties.L1LegNeverRefunded : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (st : LegState) (w : World X) (calls : List Call) (a : AssetId) (md : MintData),
    cfg.l1Router ≠ cfg.base.router → CodelessAt other cfg.l1Router →
    routerCallTo cfg cfg.l1Chain a md ∈ calls →
      claimRefund (recoverCall enc cfg.base hk other dest) st w calls = none

/-! ## Headline (c), by destination -/

/-- **HEADLINE (c), ON THE REAL CALL: A BURN'S OWN BUNDLE CALL TO ANOTHER L2 REFUNDS THE
DEPOSITOR.**  This is `AtomicRecovery.Properties.PreparedBurnRefundsDepositor` over the call the
router really produces for destination `dest`, with the explicit premise that `dest` is not the
router's `L1_CHAIN_ID`.  On a vault that knows the asset, unpaused, once the tracker hook
returns, the refund re-mints exactly the burned amount to the depositor `r.depositor`, not to
the remote receiver.  Witness: `PreparedBurnRefundToL2Satisfiable`. -/
def Properties.PreparedBurnRefundsDepositorToL2 : Prop :=
  ∀ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc),
    NativeTokenVaultBase.WellFormed s → NativeTokenVaultBase.prepare prepHooks s r = some out →
    ∀ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
      (other : Address → World X → Chain → CallData → Option (World X × Bool))
      (dest : Chain) (w : World X) (x₁ : X),
      dest ≠ cfg.l1Chain →
      w.paused = false → w.vault.originChain r.assetId ≠ cfg.base.thisChain →
      w.vault.token r.assetId ≠ 0 → hk.fromChain w.rest dest r.assetId r.data.amount = some x₁ →
        recoverCall enc cfg.base hk other dest w (routerCallTo cfg dest r.assetId out.data)
          = (hk.mint x₁ (w.vault.token r.assetId) r.depositor r.data.amount).map
              (fun x₂ => ({ w with rest := x₂ }, true))

/-- **HEADLINE (c), EXACTLY, FOR EVERY DESTINATION.**  An exact replacement of
`AtomicRecovery.Properties.PreparedBurnRefundsDepositor` on the real call.  Under that result's
premises, and `L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR`, the refund of the real call is a case
split.  To L1 it is whatever the code at the L1 router's address does.  To any other chain it is
the re-mint of the burned amount to the depositor.  Witness: `PreparedBurnRefundToL2Satisfiable`,
which also has `L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR`. -/
def Properties.PreparedBurnRefundByDestination : Prop :=
  ∀ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc),
    NativeTokenVaultBase.WellFormed s → NativeTokenVaultBase.prepare prepHooks s r = some out →
    ∀ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
      (other : Address → World X → Chain → CallData → Option (World X × Bool))
      (dest : Chain) (w : World X) (x₁ : X),
      cfg.l1Router ≠ cfg.base.router →
      w.paused = false → w.vault.originChain r.assetId ≠ cfg.base.thisChain →
      w.vault.token r.assetId ≠ 0 → hk.fromChain w.rest dest r.assetId r.data.amount = some x₁ →
        recoverCall enc cfg.base hk other dest w (routerCallTo cfg dest r.assetId out.data)
          = if dest = cfg.l1Chain then
              other cfg.l1Router w dest (.finalizeDeposit cfg.base.thisChain r.assetId (some out.data))
            else
              (hk.mint x₁ (w.vault.token r.assetId) r.depositor r.data.amount).map
                (fun x₂ => ({ w with rest := x₂ }, true))

/-- **COUNTERMODEL: THE ORIGINAL HEADLINE (c) IS FALSE FOR AN L2→L1 LEG.**  One burn to L1, with
one refund world, satisfies every premise of
`AtomicRecovery.Properties.PreparedBurnRefundsDepositor`, and the mint succeeds.  The burn goes
to the router's `L1_CHAIN_ID`, which is not the chain it is made on.  It is
prepared by the vault of the refund configuration, on its chain, called by its router, and the
refund world's registry has the burned asset's local token and origin chain as that vault has
them.  The bundle destination is the burn's own destination.  `AtomicRecovery`'s `routerCall` for
this burn is refunded to the depositor.  The call the router really produces for it, to L1, has a
refund that reverts, under the two environment premises. -/
def Properties.PreparedBurnRefundFailsToL1 : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (w : World X) (x₁ x₂ : X),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    -- the burning vault is the refund configuration's vault, on its chain, called by its router
    ∧ s.config.chainId = cfg.base.thisChain
    ∧ NativeTokenVaultBase.widen s.config.vault = cfg.base.ntv
    ∧ NativeTokenVaultBase.widen s.config.router = cfg.base.router
    ∧ NativeTokenVaultBase.widen r.caller = cfg.base.router
    -- the refund world's registry has the burned asset as the burning vault has it
    ∧ w.vault.token r.assetId = NativeTokenVaultBase.widen s.config.tokenAddress
    ∧ w.vault.originChain r.assetId = s.config.originChainId
    -- the burn goes to another chain, the router's `L1_CHAIN_ID`
    ∧ r.destinationChain ≠ cfg.base.thisChain ∧ r.destinationChain = cfg.l1Chain
    ∧ cfg.l1Router ≠ cfg.base.router ∧ CodelessAt other cfg.l1Router
    ∧ w.paused = false ∧ w.vault.originChain r.assetId ≠ cfg.base.thisChain
    ∧ w.vault.token r.assetId ≠ 0
    ∧ hk.fromChain w.rest r.destinationChain r.assetId r.data.amount = some x₁
    ∧ hk.mint x₁ (w.vault.token r.assetId) r.depositor r.data.amount = some x₂
    ∧ recoverCall enc cfg.base hk other r.destinationChain w (routerCall cfg.base r.assetId out.data)
        = some ({ w with rest := x₂ }, true)
    ∧ recoverCall enc cfg.base hk other r.destinationChain w
        (routerCallTo cfg r.destinationChain r.assetId out.data) = none

/-! ## The send side -/

/-- **THE PIN'S MODELLED CHECKS ADMIT THE ATOMIC L2→L1 LEG, AND IT IS NOT PUBLISHED.**  Take any
center whose L1 chain is not this chain, and the one-starter bundle of the router-routed starter to
L1.  It passes `PinSendChecks` both as an atomic send and as the ordinary withdrawal.  The atomic
send is appended to the manager, and the withdrawal is published to L1. -/
def Properties.PinAdmitsAtomicL1Leg : Prop :=
  ∀ (env : CenterEnv), env.l1Chain ≠ env.thisChain →
    pinSend env env.l1Chain [routerStarter env] true = some Dispatch.appendToFlow
    ∧ pinSend env env.l1Chain [routerStarter env] false = some Dispatch.publishToL1

/-- **AT THE PIN, ATOMICITY NEVER DECIDES WHETHER AN L1 SEND PASSES THE MODELLED CHECKS.**  For
every center and every list of call starters to L1, the atomic send passes `PinSendChecks`
exactly when the non-atomic send does, because the L1 checks already force every value to zero.
Only the dispatch differs.  This is about `PinSendChecks` alone.  The omitted steps that depend on
atomicity, the decoding of the `atomicBundle` attribute and the manager's `append`, are in the
`Specs` header. -/
def Properties.PinAtomicityIrrelevantToL1 : Prop :=
  ∀ (env : CenterEnv) (starters : List Starter),
    pinSend env env.l1Chain starters true
      = (pinSend env env.l1Chain starters false).map (fun _ => Dispatch.appendToFlow)

/-- **THE ONLY L1 SEND THE MODELLED CHECKS ADMIT IS THE ROUTER'S ONE STARTER.**  If a send to L1
passes `PinSendChecks`, atomic or not, its starter list is `[routerStarter env]`: one starter
(`InteropCenter.sol:382-384`), indirect, to `L2_ASSET_ROUTER_ADDR`, with zero `interopCallValue`
(`:529-537`).  So the results stated on `[routerStarter env]` cover every starter list these
checks admit for L1, for burns whose returned mint data decodes (`formedCall`). -/
def Properties.PinL1SendIsRouterStarter : Prop :=
  ∀ (env : CenterEnv) (starters : List Starter) (isAtomic : Bool) (d : Dispatch),
    pinSend env env.l1Chain starters isAtomic = some d → starters = [routerStarter env]

/-- **THE OTHER TREE'S GUARD REJECTS THE ATOMIC L1 SEND.**  It also keeps the non-atomic L1
withdrawal and every atomic send to another chain (other tree `e561b9cc2`,
`InteropCenter.sol:550-554`).  That tree is not a successor of the pin (`Specs` header). -/
def Properties.UpgradeGuardRejectsAtomicL1 : Prop :=
  ∀ (env : CenterEnv),
    ¬ UpgradeAtomicityGuard env env.l1Chain true
    ∧ UpgradeAtomicityGuard env env.l1Chain false
    ∧ ∀ dest, dest ≠ env.l1Chain → UpgradeAtomicityGuard env dest true

/-! ## Headline (d) -/

/-- **HEADLINE (d): AN ATOMIC L2→L1 LEG THAT THE PIN'S MODELLED CHECKS ADMIT IS NEVER REFUNDED.**
Premises, for every center, router, set of vault hooks and behaviour of the other targets:

* the center is on an L2 (`L1_CHAIN_ID != block.chainid`);
* the center and the router agree on `L1_CHAIN_ID`, which is one storage slot in each, and on
  `L2_ASSET_ROUTER_ADDR`;
* the two environment premises: `L1_ASSET_ROUTER` is not `L2_ASSET_ROUTER_ADDR`, and the L1
  router's address has no code on this chain.

Then, for every asset and mint data the router's burn returns:

* the atomic one-starter send to L1 passes `PinSendChecks` and is appended to the manager, not
  published to L1;
* the call the center forms from that starter is the router-produced call to L1;
* the formed bundle passes `_validateAtomicBundle`;
* the other tree's guard rejects the send;
* no claim of the formed bundle ever succeeds, in any world, whatever the leg's state.

By `PinL1SendIsRouterStarter` this starter list is the only one the modelled checks admit for an
L1 destination.  What the checks left out of `PinSendChecks` do is argued from source (`Specs`
header).  The premises are jointly satisfiable, with a prepared burn behind the mint data:
`AtomicL1LegIsStranded`. -/
def Properties.AdmittedAtomicL1LegNeverRefunded : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (env : CenterEnv) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (a : AssetId) (md : MintData),
    -- the center is on an L2
    env.l1Chain ≠ env.thisChain →
    -- the center and the router agree on `L1_CHAIN_ID` and on `L2_ASSET_ROUTER_ADDR`
    env.l1Chain = cfg.l1Chain → env.l2Router = cfg.base.router →
    -- the two environment premises
    cfg.l1Router ≠ cfg.base.router → CodelessAt other cfg.l1Router →
      pinSend env env.l1Chain [routerStarter env] true = some Dispatch.appendToFlow
      ∧ formedCall cfg env.l1Chain (routerStarter env) a md = routerCallTo cfg cfg.l1Chain a md
      ∧ AtomicBundleValid [formedCall cfg env.l1Chain (routerStarter env) a md]
      ∧ ¬ UpgradeAtomicityGuard env env.l1Chain true
      ∧ ∀ (st : LegState) (w : World X),
          claimRefund (recoverCall enc cfg.base hk other env.l1Chain) st w
            [formedCall cfg env.l1Chain (routerStarter env) a md] = none

/-! ## Concrete instances -/

/-- **HEADLINE (d), CONCRETE: AN ADMITTED L2→L1 ATOMIC LEG IS STRANDED.**  One vault, one router,
one center and one prepared burn, on one chain, that meet every premise of
`AdmittedAtomicL1LegNeverRefunded`.

* The burn is prepared by the vault of the refund configuration: the vault's chain, its own
  address and its asset router are the configuration's, and the burn is called by that router.
  It is a burn to the router's `L1_CHAIN_ID`, and it debits the depositor a positive amount.
* The center and the router agree on the L1 chain, this chain and the L2 router.  The two
  environment premises hold.
* The pin's modelled checks accept the atomic one-starter send to the burn's destination, and it
  is appended to the manager instead of published.  The call the center forms from that starter,
  with the burn's asset and mint data, is the router-produced call to L1, and the formed bundle
  passes `_validateAtomicBundle`.  The other tree's guard rejects the send.
* No claim of the formed bundle ever succeeds, in any world, whatever the leg's state. -/
def Properties.AtomicL1LegIsStranded : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : FConfig) (env : CenterEnv) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool)),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    ∧ out.state.token.balances r.depositor + out.data.amount.val = s.token.balances r.depositor
    ∧ out.data.amount ≠ 0
    -- the burning vault is the refund configuration's vault, on its chain, called by its router
    ∧ s.config.chainId = cfg.base.thisChain
    ∧ NativeTokenVaultBase.widen s.config.vault = cfg.base.ntv
    ∧ NativeTokenVaultBase.widen s.config.router = cfg.base.router
    ∧ NativeTokenVaultBase.widen r.caller = cfg.base.router
    ∧ r.destinationChain = cfg.l1Chain ∧ env.l1Chain = cfg.l1Chain
    ∧ env.thisChain = cfg.base.thisChain ∧ env.l2Router = cfg.base.router
    ∧ cfg.l1Router ≠ cfg.base.router ∧ CodelessAt other cfg.l1Router
    ∧ pinSend env r.destinationChain [routerStarter env] true = some Dispatch.appendToFlow
    ∧ formedCall cfg r.destinationChain (routerStarter env) r.assetId out.data
        = routerCallTo cfg cfg.l1Chain r.assetId out.data
    ∧ AtomicBundleValid [formedCall cfg r.destinationChain (routerStarter env) r.assetId out.data]
    ∧ ¬ UpgradeAtomicityGuard env r.destinationChain true
    ∧ ∀ (st : LegState) (w : World X),
        claimRefund (recoverCall enc cfg.base hk other r.destinationChain) st w
          [formedCall cfg r.destinationChain (routerStarter env) r.assetId out.data] = none

/-- **HEADLINE (b), CONCRETE, ON THE REAL CALLS.**  This is
`AtomicRecovery.Properties.CustomHandlerBundleIsStranded` for the router-produced calls of a
two-call atomic bundle to another L2.  The center and the router agree on the L1 chain, this
chain and the L2 router.  The two-starter send passes `PinSendChecks`, and the bundle the center
forms from the two starters is the bundle of the two router-produced calls.  A two-call bundle
cannot go to L1 (`InteropCenter.sol:382-384`).  The vault-asset call
alone would be refunded.  The bundle's claim reverts in every world reachable by steps that leave
the custom asset's registry entry alone. -/
def Properties.CustomHandlerBundleIsStrandedToL2 : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (env : CenterEnv) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (aCustom aVault : AssetId) (mdCustom mdVault : MintData),
    dest ≠ cfg.l1Chain ∧ env.l1Chain = cfg.l1Chain ∧ env.thisChain = cfg.base.thisChain
    ∧ env.l2Router = cfg.base.router
    ∧ pinSend env dest [routerStarter env, routerStarter env] true = some Dispatch.appendToFlow
    ∧ [formedCall cfg dest (routerStarter env) aCustom mdCustom,
        formedCall cfg dest (routerStarter env) aVault mdVault]
      = [routerCallTo cfg dest aCustom mdCustom, routerCallTo cfg dest aVault mdVault]
    ∧ AtomicBundleValid [routerCallTo cfg dest aCustom mdCustom, routerCallTo cfg dest aVault mdVault]
    ∧ burnHandler cfg.base w.router aCustom ≠ cfg.base.ntv
    ∧ burnHandler cfg.base w.router aVault = cfg.base.ntv
    ∧ (claimRefund (recoverCall enc cfg.base hk other dest) LegState.Revertable w
        [routerCallTo cfg dest aVault mdVault]).isSome
    ∧ ∀ w', Relation.ReflTransGen (fun u v : World X => LeavesAlone aCustom u.vault v.vault) w w' →
        claimRefund (recoverCall enc cfg.base hk other dest) LegState.Revertable w'
          [routerCallTo cfg dest aCustom mdCustom, routerCallTo cfg dest aVault mdVault] = none

/-- **WITNESS: WITHOUT THE NO-CODE PREMISE, A FOREIGN `true` CAN CLOSE THE LEG WITHOUT A REFUND.**
This is an instance, not an implication.  It exhibits one configuration with
`L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR`, one world, and code at the L1 router's address that, on
the refund call of an L1-destined bundle, returns `true` and changes nothing.  For them the claim
succeeds.  It marks the leg `Reverted`, which is terminal.  It leaves the world unchanged, vault
registry, router maps and the rest, so nothing is refunded.  This shows that the right side of
`L1LegClaimOnlyByForeignCode` is satisfiable.  That result gives the same conclusion for every
world and every code that returns `true` and changes nothing. -/
def Properties.L1LegForeignTrueClosesWithoutRefund : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (a : AssetId) (md : MintData),
    cfg.l1Router ≠ cfg.base.router ∧ dest = cfg.l1Chain
    ∧ other cfg.l1Router w dest (.finalizeDeposit cfg.base.thisChain a (some md)) = some (w, true)
    ∧ claimRefund (recoverCall enc cfg.base hk other dest) LegState.Revertable w
        [routerCallTo cfg cfg.l1Chain a md] = some (LegState.Reverted, w)

/-! ## Witnesses -/

/-- **`PreparedBurnRefundsDepositorToL2`'S PREMISES ARE JOINTLY SATISFIABLE.**  The witness is a
burn to an L2 other than the one it is made on, refunded on the burn's own destination, with
`L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR`, a depositor who is not the remote receiver, and a refund
that succeeds.  The burn is prepared by the vault of the refund configuration, on its chain,
called by its router, and the refund world's registry has the burned asset's local token and
origin chain as that vault has them. -/
def Properties.PreparedBurnRefundToL2Satisfiable : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (w : World X) (x₁ : X),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    -- the burning vault is the refund configuration's vault, on its chain, called by its router
    ∧ s.config.chainId = cfg.base.thisChain
    ∧ NativeTokenVaultBase.widen s.config.vault = cfg.base.ntv
    ∧ NativeTokenVaultBase.widen s.config.router = cfg.base.router
    ∧ NativeTokenVaultBase.widen r.caller = cfg.base.router
    -- the refund world's registry has the burned asset as the burning vault has it
    ∧ w.vault.token r.assetId = NativeTokenVaultBase.widen s.config.tokenAddress
    ∧ w.vault.originChain r.assetId = s.config.originChainId
    ∧ r.depositor ≠ r.data.receiver
    -- the burn goes to another chain, which is not the router's `L1_CHAIN_ID`
    ∧ r.destinationChain ≠ cfg.base.thisChain
    ∧ r.destinationChain ≠ cfg.l1Chain ∧ cfg.l1Router ≠ cfg.base.router
    ∧ w.paused = false ∧ w.vault.originChain r.assetId ≠ cfg.base.thisChain
    ∧ w.vault.token r.assetId ≠ 0
    ∧ hk.fromChain w.rest r.destinationChain r.assetId r.data.amount = some x₁
    ∧ outcomeOf (recoverCall enc cfg.base hk other r.destinationChain w
        (routerCallTo cfg r.destinationChain r.assetId out.data)) = Outcome.recovered

end Contracts.AssetRouter.AtomicRecoveryFaithful
