import EraSpec.Contracts.InteropCenter.Specs.AtomicRouting

/-!
# Properties: atomic legs whose recovery target has no source-side recoverer

Statements about `EraSpec.Contracts.InteropCenter.Specs.AtomicRouting`. Proofs are in
`EraSpec.Contracts.InteropCenter.Proofs.AtomicRouting`. A bare `:N` is a line of
`interop/InteropCenter.sol` at the pin. Every run starts from fresh storage (`sysInit`).

## At the pin, an atomic withdrawal to L1 is stranded (a candidate finding, fixed at `UPG`)

`sendBundle` honours the `atomicBundle` attribute for an L1 destination: the single call is the
router's withdrawal, so its `to` is the L1 asset router and its data is `finalizeDeposit(...)`
(`AtomicL1BundleCarriesL1RouterTarget`, (a)). The bundle is appended to the manager, not published,
and L1 has no `executeAtomicBundle`: under the publication premise and the run-local decoding
premise, L1's `bundleStatus` of the leg stays `Unreceived`, unless a pinned collision
(`AtomicToL1NeverExecuted`, (b)). On the L2, the refund asks the code at the L1 router's address;
with no recoverer there, every `claimRefund` of the leg reverts, unless a pinned collision
(`AtomicToL1ClaimReverts`, (c)). Together: the burn is never credited on L1 and never restored on
L2, in any continuation, or a pinned collision on named, logged preimages
(`AtomicToL1Stranded`, (d)). `AtomicToL1StrandedWitness` meets every premise of (a)–(d) on a run
in which the refund is authorized, a public withdrawal is executed on L1, and every collision
disjunct is false.

## `sendMessage` drops the attribute

`sendMessage` takes the `atomicBundle` attribute and publishes anyway (`PinAttributeRouting`), so a
leg of an "atomic" flow is executed on its own while the flow's other leg is refunded
(`SendMessageAtomicMisrouted`, (e), a countermodel run meeting the publication and `VmCall`
premises).

## Destination-side targets

For an L2 destination, a call through the router targets `L2_ASSET_ROUTER_ADDR`, the source
chain's own router, so the refund reaches it (`IndirectL2RouterLegsReachSourceRouter`, (f); with
`AtomicFlowManager.Properties.SourceRouterTargetRefundsDepositor` it refunds the depositor). Any
other call's `to` is a destination-side address; if no recoverer is deployed there on the source
chain, the leg is never refunded (`NonRecovererLegNeverRefunded`, (g)), e.g. a router deposit
followed by a call to a destination-only application (`NonRecovererLegNeverRefundedWitness`).

## The repair

With `isAtomic → dest ≠ L1` in `sendBundle` and a revert on the attribute in `sendMessage`, every
logged send is atomic iff it carried the attribute, and every atomic one goes to a destination with
an atomic entry point (`AttributeHonouredOrRejected`, (i)); no atomic leg to L1 exists, so (c)
and (d) apply to no leg (`RepairedNoAtomicLegToL1`). At the pin both conjuncts fail
(`PinBreaksAttributeHonoured`). `AttributeHonouredOrRejectedWitness` is a repaired run with an
atomic leg, a `sendMessage` and a withdrawal.
-/

namespace Contracts.InteropCenter.AtomicRouting

open Contracts.AtomicFlowManager (LegState)
open Contracts.AtomicFlowManager.RecoveryTargets (CallSem VmCall NoRecovererAt recoverStep
  claimRefund)
open AttackVectors.BundleStatusMachine (Status)

/-! ## (a) Routing -/

/-- **(a) AN L1-DESTINED BUNDLE CARRIES ONE CALL, TO THE L1 ROUTER.** Along any run, with or without
the repairs, every logged send to L1 has exactly one call; its `to` is the router's
`L1_ASSET_ROUTER`, its `from` is the L2 router, its value is zero, and its data is
`finalizeDeposit(block.chainid, assetId, mintData)` for the burned asset. So the refund loop asks
the code deployed at the L1 router's address on this L2. -/
def Properties.AtomicL1BundleCarriesL1RouterTarget : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    ∀ s ∈ S.sends, s.dest = E.l1ChainId →
      ∃ c, s.dispatch.bundle.calls = [c] ∧ c.target = E.l1Router ∧ c.fromAddr = E.l2Router ∧
        c.value = 0 ∧ (∃ (assetId : Word) (mintData : List UInt8),
          c.data = E.depositCalldata E.P.chainId assetId mintData) ∧
        ∀ w, recoverStep E.sem E.code InteropCall.target InteropCall.data s.dest w c
          = E.sem (E.code E.l1Router) w s.dest c.data

/-- **HOW EACH ENTRY POINT ROUTES THE ATTRIBUTE.** Along any run, with or without the repairs: a
`sendMessage` is never atomic, whatever its attributes (:252); a `sendBundle` is atomic exactly
when it carried the `atomicBundle` attribute (:318, :874-883), whatever its destination unless the
repair is in place. -/
def Properties.PinAttributeRouting : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    ∀ s ∈ S.sends, (s.entry = .sendMessage → s.dispatch.isAtomic = false) ∧
      (s.entry = .sendBundle → (s.dispatch.isAtomic = true ↔ s.attr.isSome = true))

/-! ## (b)–(d) An atomic leg to L1 -/

/-- **(b) NO ATOMIC BUNDLE IS EVER EXECUTED ON L1, OR A PINNED COLLISION.** Along any run, with
or without the repairs: assume the publication premise (`CenterPublishesOnlyPublicDispatches`) and
the run-local decoding premise (`DecodesRunBundles`, which also makes the encoder injective on the
run's bundles, the premise of `Dispatch`'s `AtomicBytesNeverPublished`). Then for
every atomic dispatch `d` of the run, L1's `bundleStatus` at `d`'s bundle hash is `Unreceived`
(neither verified, executed nor unbundled), or two different senders used the same salt and keccak
collides on their packed preimages (`CrossSenderSaltClash`, with a public dispatch of the run), or
keccak collides on `d`'s bundle-hash preimage and the preimage of bytes L1's handler accepted. L1 has
no `executeAtomicBundle` (`L1InteropHandler.sol:30-94`), and its other entry points need an
inclusion proof of a published message (`InteropHandlerBase.sol:296-316`). -/
def Properties.AtomicToL1NeverExecuted : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    CenterPublishesOnlyPublicDispatches E S → DecodesRunBundles E S →
    ∀ d ∈ S.src.log, d.isAtomic = true →
      (S.dst E.l1ChainId).status (bundleHash E.P d.bundle) = .Unreceived ∨
      (∃ d' ∈ S.src.log, d'.isAtomic = false ∧ CrossSenderSaltClash E.P d d') ∨
      (∃ x ∈ (S.dst E.l1ChainId).verified, claimPreimage E.dec x ≠ bundlePreimage E.P d.bundle ∧
        E.P.keccak (claimPreimage E.dec x) = bundleHash E.P d.bundle)

/-- **(c) EVERY `claimRefund` OF AN ATOMIC LEG TO L1 REVERTS, OR A PINNED COLLISION.** Along any
run, under `VmCall` and with no recoverer at the L1 router's address on this L2, and with the
decoder inverting the encoder on the run's bundles: for an atomic dispatch `d` to L1 and any bytes
`x` that `claimRefund` hashes to `d`'s bundle hash, the claim reverts in every world and for every
leg state, or `x`'s preimage differs from `d`'s (so keccak collides on two named preimages). -/
def Properties.AtomicToL1ClaimReverts : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    VmCall E.sem → NoRecovererAt E.code E.l1Router → DecodesRunBundles E S →
    ∀ d ∈ S.src.log, d.isAtomic = true → d.bundle.destinationChainId = E.l1ChainId →
      ∀ x : List UInt8, handlerHash E x = bundleHash E.P d.bundle →
        (∀ (st : LegState) (w : W), claimRefund (refundStep E x) st w (E.dec x).calls = none) ∨
        claimPreimage E.dec x ≠ bundlePreimage E.P d.bundle

/-- **(g) A LEG WITH A NON-RECOVERER TARGET IS NEVER REFUNDED, OR A PINNED COLLISION.** Along any
run, under `VmCall` and with the decoder inverting the encoder on the run's bundles: if some call
of an atomic dispatch `d` targets an address with no recoverer on the source chain, `d`'s leg is
not `Reverted`, or some logged successful claim hashed bytes whose preimage differs from `d`'s to
`d`'s bundle hash. Since every reachable state satisfies it, this holds in every continuation. -/
def Properties.NonRecovererLegNeverRefunded : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    VmCall E.sem → DecodesRunBundles E S →
    ∀ d ∈ S.src.log, d.isAtomic = true → (∃ c ∈ d.bundle.calls, NoRecovererAt E.code c.target) →
      S.src.manager.legState d.atomicSend.flowId (bundleHash E.P d.bundle) ≠ .Reverted ∨
      ∃ p ∈ S.claims, claimPreimage E.dec p.2 ≠ bundlePreimage E.P d.bundle ∧
        E.P.keccak (claimPreimage E.dec p.2) = bundleHash E.P d.bundle

/-- **(d) HEADLINE: AN ATOMIC WITHDRAWAL TO L1 IS STRANDED, OR A LOCATED BREAK.** Along any run, with
or without the repairs, under `VmCall`, no recoverer at the L1 router's address on this L2, the
publication premise and the run-local decoding premise: for every atomic dispatch `d` to L1,
(1) L1 has not verified, executed or unbundled it (so the burn is not credited on L1), or the
cross-sender salt clash, or a keccak collision with bytes L1's handler accepted; and (2) its leg is
not `Reverted` (so the burn is not restored on the L2), or a keccak collision with bytes of a logged
successful claim. Every reachable state satisfies both, so no continuation resolves the burn. -/
def Properties.AtomicToL1Stranded : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    VmCall E.sem → NoRecovererAt E.code E.l1Router → CenterPublishesOnlyPublicDispatches E S →
    DecodesRunBundles E S →
    ∀ d ∈ S.src.log, d.isAtomic = true → d.bundle.destinationChainId = E.l1ChainId →
      ((S.dst E.l1ChainId).status (bundleHash E.P d.bundle) = .Unreceived ∨
        (∃ d' ∈ S.src.log, d'.isAtomic = false ∧ CrossSenderSaltClash E.P d d') ∨
        (∃ x ∈ (S.dst E.l1ChainId).verified, claimPreimage E.dec x ≠ bundlePreimage E.P d.bundle ∧
          E.P.keccak (claimPreimage E.dec x) = bundleHash E.P d.bundle)) ∧
      (S.src.manager.legState d.atomicSend.flowId (bundleHash E.P d.bundle) ≠ .Reverted ∨
        ∃ p ∈ S.claims, claimPreimage E.dec p.2 ≠ bundlePreimage E.P d.bundle ∧
          E.P.keccak (claimPreimage E.dec p.2) = bundleHash E.P d.bundle)

/-! ## (e) `sendMessage` -/

/-- **(e) COUNTERMODEL: `sendMessage` MISROUTES THE ATTRIBUTE.** A run of the pinned code meeting
`VmCall`, the publication premise and the decoding premise, with two sends carrying the
`atomicBundle` attribute of the same flow to the same destination: a `sendMessage`, published and
never appended (its leg stays `Unset`), and a `sendBundle`, appended. Both bundle hashes are legs of
the flow. The destination has executed the first (`FullyExecuted`, through the public
`executeBundle`), and the source has refunded the second (`Reverted`, after `authorizeRefund` saw
the first leg missing from the tree). -/
def Properties.SendMessageAtomicMisrouted : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach pin E (sysInit w₀) S ∧
    VmCall E.sem ∧ CenterPublishesOnlyPublicDispatches E S ∧ DecodesRunBundles E S ∧
    ∃ (s₁ s₂ : Send) (a : AtomicAttr), s₁ ∈ S.sends ∧ s₂ ∈ S.sends ∧
      s₁.entry = .sendMessage ∧ s₁.attr = some a ∧ s₂.attr = some a ∧
      s₁.dispatch.isAtomic = false ∧ s₂.dispatch.isAtomic = true ∧ s₁.dest = s₂.dest ∧
      (bundleHash E.P s₁.dispatch.bundle, E.P.chainId) ∈ E.flowLegs a.flowId ∧
      (bundleHash E.P s₂.dispatch.bundle, E.P.chainId) ∈ E.flowLegs a.flowId ∧
      bundleHash E.P s₁.dispatch.bundle ≠ bundleHash E.P s₂.dispatch.bundle ∧
      S.src.manager.legState a.flowId (bundleHash E.P s₁.dispatch.bundle) = .Unset ∧
      (S.dst s₁.dest).status (bundleHash E.P s₁.dispatch.bundle) = .FullyExecuted ∧
      S.src.manager.legState a.flowId (bundleHash E.P s₂.dispatch.bundle) = .Reverted

/-! ## (f) L2 router legs -/

/-- **(f) AN INDIRECT ROUTER CALL TO AN L2 TARGETS THE SOURCE CHAIN'S OWN ROUTER.** Along any run,
with or without the repairs, for every logged send to an L2 and every call formed from an indirect
starter through the L2 router: its `to` and `from` are `L2_ASSET_ROUTER_ADDR`, its data is
`finalizeDeposit(block.chainid, assetId, mintData)`, and the refund loop asks the code at the
router's own address on this chain. -/
def Properties.IndirectL2RouterLegsReachSourceRouter : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    ∀ s ∈ S.sends, s.dest ≠ E.l1ChainId →
      List.Forall₂ (fun cs c => cs.callAttributes.indirectCall = true → cs.target = E.l2Router →
          c.target = E.l2Router ∧ c.fromAddr = E.l2Router ∧
          (∃ (assetId : Word) (mintData : List UInt8),
            c.data = E.depositCalldata E.P.chainId assetId mintData) ∧
          ∀ w, recoverStep E.sem E.code InteropCall.target InteropCall.data s.dest w c
            = E.sem (E.code E.l2Router) w s.dest c.data)
        s.dispatch.starters s.dispatch.bundle.calls

/-! ## (i) The repair -/

/-- **(i) UNDER THE REPAIRS, THE ATTRIBUTE IS HONOURED OR THE SEND IS REJECTED.** Along any run of
the repaired code, every logged send is atomic exactly when it carried the `atomicBundle`
attribute, and every atomic one goes to a destination whose handler has `executeAtomicBundle`. -/
def Properties.AttributeHonouredOrRejected : Prop :=
  ∀ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach repaired E (sysInit w₀) S →
    ∀ s ∈ S.sends, (s.dispatch.isAtomic = true ↔ s.attr.isSome = true) ∧
      (s.dispatch.isAtomic = true → atomicEntry (destKind E s.dest) = true)

/-- **UNDER THE REPAIRS, NO ATOMIC LEG GOES TO L1**: along any run of the repaired code, no logged
atomic dispatch has destination L1, so (c) and (d) apply to no leg. -/
def Properties.RepairedNoAtomicLegToL1 : Prop :=
  ∀ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach repaired E (sysInit w₀) S →
    ∀ d ∈ S.src.log, d.isAtomic = true → d.bundle.destinationChainId ≠ E.l1ChainId

/-- **AT THE PIN BOTH CONJUNCTS OF (i) FAIL.** A run of the pinned code with a send that carried the
attribute and is not atomic, and an atomic send to a destination without an atomic entry point. -/
def Properties.PinBreaksAttributeHonoured : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach pin E (sysInit w₀) S ∧
    (∃ s ∈ S.sends, s.attr.isSome = true ∧ s.dispatch.isAtomic = false) ∧
    (∃ s ∈ S.sends, s.dispatch.isAtomic = true ∧ atomicEntry (destKind E s.dest) = false)

/-! ## Witnesses -/

/-- **THE PREMISES OF (a)–(d) HOLD ON A RUN IN WHICH THE WITHDRAWAL IS STRANDED, AND NO BREAK
HOLDS.** A run of the pinned code under `VmCall`, with nothing deployed at the L1 router's address,
the publication premise and the decoding premise. It has an atomic withdrawal `d` to L1, whose
logged send is (a)'s premise, whose refund has been authorized (the leg is `Revertable`) and which
L1 has not received, while a public withdrawal of the same run is `FullyExecuted` on L1. Every
collision disjunct of (b) and (d) is false, and for (c) the leg's own bytes hash to its bundle hash
with the same preimage, so (c)'s collision disjunct is false and every claim of them reverts. -/
def Properties.AtomicToL1StrandedWitness : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach pin E (sysInit w₀) S ∧
    VmCall E.sem ∧ NoRecovererAt E.code E.l1Router ∧ CenterPublishesOnlyPublicDispatches E S ∧
    DecodesRunBundles E S ∧
    ∃ d ∈ S.src.log, d.isAtomic = true ∧ d.bundle.destinationChainId = E.l1ChainId ∧
      (∃ s ∈ S.sends, s.dispatch = d ∧ s.dest = E.l1ChainId) ∧
      S.src.manager.legState d.atomicSend.flowId (bundleHash E.P d.bundle) = .Revertable ∧
      (S.dst E.l1ChainId).status (bundleHash E.P d.bundle) = .Unreceived ∧
      (∃ d' ∈ S.src.log, d'.isAtomic = false ∧ d'.bundle.destinationChainId = E.l1ChainId ∧
        (S.dst E.l1ChainId).status (bundleHash E.P d'.bundle) = .FullyExecuted) ∧
      (¬ ∃ d' ∈ S.src.log, d'.isAtomic = false ∧ CrossSenderSaltClash E.P d d') ∧
      (∀ x ∈ (S.dst E.l1ChainId).verified, handlerHash E x ≠ bundleHash E.P d.bundle) ∧
      (∀ p ∈ S.claims, handlerHash E p.2 ≠ bundleHash E.P d.bundle) ∧
      handlerHash E (E.P.enc d.bundle) = bundleHash E.P d.bundle ∧
      claimPreimage E.dec (E.P.enc d.bundle) = bundlePreimage E.P d.bundle

/-- **THE PREMISES OF (g) HOLD ON A ROUTER DEPOSIT FOLLOWED BY A CALL TO A DESTINATION-ONLY
APPLICATION.** On the same pinned run, under `VmCall` and the decoding premise: an atomic leg to an
L2 whose calls are a router deposit and a direct call to an address with nothing deployed on the
source chain. Its refund has been authorized (`Revertable`), its router call alone would be
refunded, and no logged claim hashed to its bundle hash. -/
def Properties.NonRecovererLegNeverRefundedWitness : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach pin E (sysInit w₀) S ∧
    VmCall E.sem ∧ DecodesRunBundles E S ∧
    ∃ d ∈ S.src.log, d.isAtomic = true ∧ d.bundle.destinationChainId ≠ E.l1ChainId ∧
      (∃ c ∈ d.bundle.calls, NoRecovererAt E.code c.target) ∧
      (∃ c ∈ d.bundle.calls,
        (claimRefund (refundStep E (E.P.enc d.bundle)) .Revertable S.world [c]).isSome = true) ∧
      S.src.manager.legState d.atomicSend.flowId (bundleHash E.P d.bundle) = .Revertable ∧
      (∀ p ∈ S.claims, handlerHash E p.2 ≠ bundleHash E.P d.bundle)

/-- **THE PREMISES OF (f) HOLD**: on the same pinned run, a logged send to an L2 with an indirect
starter through the L2 router. -/
def Properties.IndirectL2RouterLegsReachSourceRouterWitness : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach pin E (sysInit w₀) S ∧
    ∃ s ∈ S.sends, s.dest ≠ E.l1ChainId ∧ ∃ cs ∈ s.dispatch.starters,
      cs.callAttributes.indirectCall = true ∧ cs.target = E.l2Router

/-- **THE PREMISES OF (i) HOLD ON A NONTRIVIAL REPAIRED RUN**: an atomic leg (to an L2), a
`sendMessage` (published), and a withdrawal to L1. -/
def Properties.AttributeHonouredOrRejectedWitness : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach repaired E (sysInit w₀) S ∧
    (∃ s ∈ S.sends, s.dispatch.isAtomic = true ∧ s.attr.isSome = true) ∧
    (∃ s ∈ S.sends, s.entry = .sendMessage ∧ s.dispatch.isAtomic = false) ∧
    (∃ s ∈ S.sends, s.dest = E.l1ChainId)

end Contracts.InteropCenter.AtomicRouting
