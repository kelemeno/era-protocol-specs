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
  with nothing refunded (`L1LegForeignTrueClosesWithoutRefund`).  With no code at that address,
  the refund reverts (`L1LegRefundReverts`) and every claim of the bundle reverts
  (`L1LegNeverRefunded`).
* **The original headline (c) is false for an L2→L1 leg.**  One prepared burn to L1 satisfies
  every premise of `AtomicRecovery.Properties.PreparedBurnRefundsDepositor`, and its modelled call
  is refunded, but its real call's refund reverts (`PreparedBurnRefundFailsToL1`).  The strongest
  true replacement is the case split `PreparedBurnRefundByDestination`.
* **The pin admits such a leg, and the upgrade does not.**  At the pin, atomicity never changes
  whether an L1 send passes `PinSendChecks`.  It only turns publication into an `append`
  (`PinAtomicityIrrelevantToL1`, `PinAdmitsAtomicL1Leg`).  The upgrade's guard rejects the atomic
  L1 send and keeps the L1 withdrawal and atomic sends to other chains
  (`UpgradeGuardRejectsAtomicL1`).
* **Headline (d): `AtomicL1LegIsStranded`.**  A burn to L1 debits the depositor, and the pin admits
  its atomic bundle and appends it instead of publishing it.  No claim of that bundle ever
  succeeds, in any world, whatever the leg's state.  Since L1 executes only published bundles
  (`Specs` header), the burned amount is neither minted on L1 nor refunded.

Environment premises: `L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR` (`OPS-CONFIG`) and
`CodelessAt other L1_ASSET_ROUTER` (`VM-CALL`, about that one address).  Both are satisfied by the
witnesses.  No result takes a hash premise.
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

/-- **HEADLINE (c), EXACTLY, FOR EVERY DESTINATION.**  The strongest true replacement of
`AtomicRecovery.Properties.PreparedBurnRefundsDepositor`.  Under that result's premises, and
`L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR`, the refund of the real call is a case split.  To L1 it is
whatever the code at the L1 router's address does.  To any other chain it is the re-mint of the
burned amount to the depositor.  Witness: `PreparedBurnRefundToL2Satisfiable`, which also has
`L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR`. -/
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
`AtomicRecovery.Properties.PreparedBurnRefundsDepositor`, and the mint succeeds.  The bundle
destination is the burn's own destination.  `AtomicRecovery`'s `routerCall` for this burn is
refunded to the depositor.  The call the router really produces for it, to L1, has a refund that
reverts, under the two environment premises. -/
def Properties.PreparedBurnRefundFailsToL1 : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (w : World X) (x₁ x₂ : X),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    ∧ r.destinationChain = cfg.l1Chain
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

/-- **THE PIN ADMITS THE ATOMIC L2→L1 LEG, AND DOES NOT PUBLISH IT.**  Take any center whose L1
chain is not this chain, and the one-starter bundle of the router-routed starter to L1.  It passes
`PinSendChecks` both as an atomic send and as the ordinary withdrawal.  The atomic send is
appended to the manager, and the withdrawal is published to L1. -/
def Properties.PinAdmitsAtomicL1Leg : Prop :=
  ∀ (env : CenterEnv), env.l1Chain ≠ env.thisChain →
    pinSend env env.l1Chain [routerStarter env] true = some Dispatch.appendToFlow
    ∧ pinSend env env.l1Chain [routerStarter env] false = some Dispatch.publishToL1

/-- **AT THE PIN, ATOMICITY NEVER DECIDES AN L1 SEND.**  For every center and every list of call
starters to L1, the atomic send passes `PinSendChecks` exactly when the non-atomic send does,
because the L1 checks already force every value to zero.  Only the dispatch differs. -/
def Properties.PinAtomicityIrrelevantToL1 : Prop :=
  ∀ (env : CenterEnv) (starters : List Starter),
    pinSend env env.l1Chain starters true
      = (pinSend env env.l1Chain starters false).map (fun _ => Dispatch.appendToFlow)

/-- **THE UPGRADE'S GUARD REJECTS THE ATOMIC L1 SEND.**  It also keeps the non-atomic L1
withdrawal and every atomic send to another chain (upgrade `InteropCenter.sol:550-554`). -/
def Properties.UpgradeGuardRejectsAtomicL1 : Prop :=
  ∀ (env : CenterEnv),
    ¬ UpgradeAtomicityGuard env env.l1Chain true
    ∧ UpgradeAtomicityGuard env env.l1Chain false
    ∧ ∀ dest, dest ≠ env.l1Chain → UpgradeAtomicityGuard env dest true

/-! ## Concrete instances -/

/-- **HEADLINE (d), CONCRETE: AN ADMITTED L2→L1 ATOMIC LEG IS STRANDED.**  One prepared burn to
L1 debits the depositor a positive amount.  The center and the router agree on the L1 chain, this
chain and the L2 router.  The two environment premises hold.  The pin accepts the atomic one-call
bundle and appends it to the manager instead of publishing it, and the bundle passes
`_validateAtomicBundle`.  The upgrade's guard rejects it.  No claim of the bundle ever succeeds,
in any world, whatever the leg's state. -/
def Properties.AtomicL1LegIsStranded : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : FConfig) (env : CenterEnv) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool)),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    ∧ out.state.token.balances r.depositor + out.data.amount.val = s.token.balances r.depositor
    ∧ out.data.amount ≠ 0
    ∧ r.destinationChain = cfg.l1Chain ∧ env.l1Chain = cfg.l1Chain
    ∧ env.thisChain = cfg.base.thisChain ∧ env.l2Router = cfg.base.router
    ∧ cfg.l1Router ≠ cfg.base.router ∧ CodelessAt other cfg.l1Router
    ∧ pinSend env r.destinationChain [routerStarter env] true = some Dispatch.appendToFlow
    ∧ AtomicBundleValid [routerCallTo cfg r.destinationChain r.assetId out.data]
    ∧ ¬ UpgradeAtomicityGuard env r.destinationChain true
    ∧ ∀ (st : LegState) (w : World X),
        claimRefund (recoverCall enc cfg.base hk other r.destinationChain) st w
          [routerCallTo cfg r.destinationChain r.assetId out.data] = none

/-- **HEADLINE (b), CONCRETE, ON THE REAL CALLS.**  This is
`AtomicRecovery.Properties.CustomHandlerBundleIsStranded` for the router-produced calls of a
two-call atomic bundle to another L2.  The bundle passes `PinSendChecks`.  A two-call bundle
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
    ∧ AtomicBundleValid [routerCallTo cfg dest aCustom mdCustom, routerCallTo cfg dest aVault mdVault]
    ∧ burnHandler cfg.base w.router aCustom ≠ cfg.base.ntv
    ∧ burnHandler cfg.base w.router aVault = cfg.base.ntv
    ∧ (claimRefund (recoverCall enc cfg.base hk other dest) LegState.Revertable w
        [routerCallTo cfg dest aVault mdVault]).isSome
    ∧ ∀ w', Relation.ReflTransGen (fun u v : World X => LeavesAlone aCustom u.vault v.vault) w w' →
        claimRefund (recoverCall enc cfg.base hk other dest) LegState.Revertable w'
          [routerCallTo cfg dest aCustom mdCustom, routerCallTo cfg dest aVault mdVault] = none

/-- **WITHOUT THE NO-CODE PREMISE, A FOREIGN `true` CLOSES THE LEG WITHOUT A REFUND.**  Suppose
the code at the L1 router's address returns `true` and changes nothing.  Then the claim succeeds,
which is the right side of `L1LegClaimOnlyByForeignCode`.  It marks the leg `Reverted`, which is
terminal.  It leaves the world unchanged, vault registry, router maps and the rest, so nothing is
refunded. -/
def Properties.L1LegForeignTrueClosesWithoutRefund : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (a : AssetId) (md : MintData),
    cfg.l1Router ≠ cfg.base.router
    ∧ claimRefund (recoverCall enc cfg.base hk other dest) LegState.Revertable w
        [routerCallTo cfg cfg.l1Chain a md] = some (LegState.Reverted, w)

/-! ## Witnesses -/

/-- **`PreparedBurnRefundsDepositorToL2`'S PREMISES ARE JOINTLY SATISFIABLE.**  The witness is a
burn to an L2, refunded on the burn's own destination, with
`L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR`, a depositor who is not the remote receiver, and a refund
that succeeds. -/
def Properties.PreparedBurnRefundToL2Satisfiable : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : FConfig) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (w : World X) (x₁ : X),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    ∧ r.depositor ≠ r.data.receiver
    ∧ r.destinationChain ≠ cfg.l1Chain ∧ cfg.l1Router ≠ cfg.base.router
    ∧ w.paused = false ∧ w.vault.originChain r.assetId ≠ cfg.base.thisChain
    ∧ w.vault.token r.assetId ≠ 0
    ∧ hk.fromChain w.rest r.destinationChain r.assetId r.data.amount = some x₁
    ∧ outcomeOf (recoverCall enc cfg.base hk other r.destinationChain w
        (routerCallTo cfg r.destinationChain r.assetId out.data)) = Outcome.recovered

end Contracts.AssetRouter.AtomicRecoveryFaithful
