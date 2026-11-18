import EraSpec.Contracts.InteropCenter.Specs.AtomicRouting

/-!
# Properties: where an atomic leg's calls point, and an atomic leg sent to L1

Statements about `EraSpec.Contracts.InteropCenter.Specs.AtomicRouting`. Proofs are in
`EraSpec.Contracts.InteropCenter.Proofs.AtomicRouting`. A bare `:N` is a line of
`interop/InteropCenter.sol` at the pin. Every run starts from fresh storage (`sysInit`). `pin` is
the pinned code; `upgradeTree` adds the two checks of `e561b9cc2` that decide where the
`atomicBundle` attribute goes (`Guards`).

## How the attribute is routed

A logged send is atomic exactly when it carried the attribute and came through `sendBundle`, or
through `sendMessage` where `sendMessage` honours the attribute (`AttributeRoutingByEntryPoint`).
So at the pin a `sendMessage` carrying the attribute is published, and `SendMessageAtomicMisrouted`
is a pinned run in which it is a leg of a flow: the destination executes it while the source
refunds the flow's other leg. This models the `sendMessage` finding recorded in this folder's
README.

## An atomic leg to L1 at the pin

The pin's checks admit an atomic `sendBundle` to L1 (the case recorded in
`AssetRouterBase/README.md`). Its single call is the router's withdrawal: `to` the router's
`L1_ASSET_ROUTER`, `from` the L2 router, value zero, data `finalizeDeposit(...)`, and the refund loop
asks the code at the L1 router's address on this L2 (`AtomicL1BundleCarriesL1RouterTarget`, (a)).
Under the publication premise and the run-local decoding premise, L1's `bundleStatus` of the leg is
`Unreceived`, unless a pinned collision (`AtomicToL1NeverExecuted`, (b)). Under `VmCall` and with
no recoverer at the L1 router's address on this L2, every `claimRefund` of the leg's bytes reverts,
unless a pinned collision (`AtomicToL1ClaimReverts`, (c)). Together, (d) `AtomicToL1Stranded`: in
every reachable state L1 has not verified, executed or unbundled the leg, and the leg is not
`Reverted`, each up to a pinned collision on named, logged preimages. `AtomicToL1StrandedWitness`
meets every premise of (a)–(d) on a pinned run in which the leg's refund is authorized and a
public withdrawal is executed on L1, and every collision disjunct is false. Two pinned runs show the
premises are needed: with an inclusion verdict that accepts the leg's bytes, L1 executes the leg
(`AtomicToL1StrandedNeedsPublicationPremise`); with code at the L1 router's address that returns
`true`, the leg is claimed and `Reverted` (`AtomicToL1StrandedNeedsNoRecoverer`).

## Targets on the source chain

(f): a call formed from an indirect starter through the router, in a send to an L2, targets
`L2_ASSET_ROUTER_ADDR`, so the refund loop asks the code at the router's own address on this chain
(`IndirectL2RouterLegsReachSourceRouter`). What a router recoverer deployed there does is stated on
`AssetRouterBase`'s router model by `AtomicFlowManager`'s `SourceRouterTargetRefundsDepositor`; the
two models are not composed in Lean.
(g): if some call of an atomic leg targets an address with no recoverer on the source chain, the
leg is not `Reverted`, up to a pinned collision with a logged claim
(`NonRecovererLegNeverRefunded`). `NonRecovererLegNeverRefundedWitness` meets its premises (in the
proof, with a router call and a direct call to an address with nothing deployed on the source
chain).

## The other tree's checks

With both checks, every logged send is atomic exactly when it carried the attribute, and every
atomic one goes to a destination whose handler has `executeAtomicBundle`
(`AttributeHonouredOrRejected`, (i)). With the L1 check alone no atomic leg goes to L1, so (c) and
(d) apply to no leg (`GuardKeepsAtomicLegsOffL1`). At the pin both conjuncts of (i) fail
(`PinBreaksAttributeHonoured`). `AttributeHonouredOrRejectedWitness` is an `upgradeTree` run with an
atomic `sendBundle`, an atomic `sendMessage`, a `sendMessage` that is not atomic and a send to L1; its
run also meets the premises of `GuardKeepsAtomicLegsOffL1`. `AttributeRoutingByEntryPointWitness`
exercises every case of `AttributeRoutingByEntryPoint`, and `AtomicToL1StrandedWitness`'s run has a
logged send to L1, the premise of (a).
-/

namespace Contracts.InteropCenter.AtomicRouting

open Contracts.AtomicFlowManager (LegState)
open Contracts.AtomicFlowManager.RecoveryTargets (CallSem VmCall NoRecovererAt recoverStep
  claimRefund)
open AttackVectors.BundleStatusMachine (Status)

/-! ## Attribute routing -/

/-- **HOW EACH ENTRY POINT ROUTES THE ATTRIBUTE.** Along any run, for any `Guards`: a logged send is
atomic exactly when it carried the `atomicBundle` attribute and either came through `sendBundle`
(:318, :874-883) or came through `sendMessage` with `K.messageHonoursAtomic` set. So at the pin a
`sendMessage` is never atomic, whatever its attributes (:252). -/
def Properties.AttributeRoutingByEntryPoint : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    ∀ s ∈ S.sends, (s.dispatch.isAtomic = true ↔
      s.attr.isSome = true ∧ (s.entry = .sendBundle ∨ K.messageHonoursAtomic = true))

/-! ## (a) Routing to L1 -/

/-- **(a) AN L1-DESTINED BUNDLE CARRIES ONE CALL, TO THE L1 ROUTER.** Along any run, for any
`Guards`, every logged send to L1 has exactly one call. Its `to` is the router's `L1_ASSET_ROUTER`,
its `from` is the L2 router, its value is zero, and its data is
`finalizeDeposit(block.chainid, assetId, mintData)` for some asset id and mint data (the burn that
produced them is not modelled). So the refund loop's call of it is the code at the L1 router's
address on this L2. -/
def Properties.AtomicL1BundleCarriesL1RouterTarget : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    ∀ s ∈ S.sends, s.dest = E.l1ChainId →
      ∃ c, s.dispatch.bundle.calls = [c] ∧ c.target = E.l1Router ∧ c.fromAddr = E.l2Router ∧
        c.value = 0 ∧ (∃ (assetId : Word) (mintData : List UInt8),
          c.data = E.depositCalldata E.P.chainId assetId mintData) ∧
        ∀ w, recoverStep E.sem E.code InteropCall.target InteropCall.data s.dest w c
          = E.sem (E.code E.l1Router) w s.dest c.data

/-! ## (b)–(d) An atomic leg to L1 -/

/-- **(b) L1 NEVER RECEIVES AN ATOMIC BUNDLE OF THE RUN, OR A PINNED COLLISION.** Along any run, for
any `Guards`: assume the publication premise (`CenterPublishesOnlyPublicDispatches`) and the
run-local decoding premise (`DecodesRunBundles`, which also gives `Dispatch`'s `EncInjOn` on the
run's bundles, the premise of `AtomicBytesNeverPublished`). Then for every atomic dispatch `d` of
the run, L1's `bundleStatus` at `d`'s bundle hash is `Unreceived` (not verified, executed or
unbundled); or two different senders used the same salt and keccak collides on their packed
preimages (`CrossSenderSaltClash` with a public dispatch of the run); or keccak collides on `d`'s
bundle-hash preimage and the preimage of bytes L1's handler accepted. In the model L1's handler has
no `executeAtomic` step (`atomicEntry`; `L1InteropHandler.sol:30-94`). -/
def Properties.AtomicToL1NeverExecuted : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    CenterPublishesOnlyPublicDispatches E S → DecodesRunBundles E S →
    ∀ d ∈ S.src.log, d.isAtomic = true →
      (S.dst E.l1ChainId).status (bundleHash E.P d.bundle) = .Unreceived ∨
      (∃ d' ∈ S.src.log, d'.isAtomic = false ∧ CrossSenderSaltClash E.P d d') ∨
      (∃ x ∈ (S.dst E.l1ChainId).verified, claimPreimage E.dec x ≠ bundlePreimage E.P d.bundle ∧
        E.P.keccak (claimPreimage E.dec x) = bundleHash E.P d.bundle)

/-- **(c) EVERY `claimRefund` OF AN ATOMIC LEG TO L1 REVERTS, OR A PINNED COLLISION.** Along any
run, for any `Guards`, under `VmCall`, with no recoverer at the L1 router's address on this L2, and
with the decoder inverting the encoder on the run's bundles: for an atomic dispatch `d` to L1 and
any bytes `x` that `claimRefund` hashes to `d`'s bundle hash, the claim of `x` reverts in every
world and for every leg state, or `x`'s hash preimage differs from `d`'s (two named preimages with
one keccak). -/
def Properties.AtomicToL1ClaimReverts : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    VmCall E.sem → NoRecovererAt E.code E.l1Router → DecodesRunBundles E S →
    ∀ d ∈ S.src.log, d.isAtomic = true → d.bundle.destinationChainId = E.l1ChainId →
      ∀ x : List UInt8, handlerHash E x = bundleHash E.P d.bundle →
        (∀ (st : LegState) (w : W), claimRefund (refundStep E x) st w (E.dec x).calls = none) ∨
        claimPreimage E.dec x ≠ bundlePreimage E.P d.bundle

/-- **(g) A LEG WITH A NON-RECOVERER TARGET IS NOT REFUNDED, OR A PINNED COLLISION.** Along any run,
for any `Guards`, under `VmCall` and with the decoder inverting the encoder on the run's bundles: if
some call of an atomic dispatch `d` targets an address with no recoverer on the source chain, `d`'s
leg is not `Reverted`, or some logged successful claim hashed bytes whose preimage differs from
`d`'s to `d`'s bundle hash. -/
def Properties.NonRecovererLegNeverRefunded : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), SysReach K E (sysInit w₀) S →
    VmCall E.sem → DecodesRunBundles E S →
    ∀ d ∈ S.src.log, d.isAtomic = true → (∃ c ∈ d.bundle.calls, NoRecovererAt E.code c.target) →
      S.src.manager.legState d.atomicSend.flowId (bundleHash E.P d.bundle) ≠ .Reverted ∨
      ∃ p ∈ S.claims, claimPreimage E.dec p.2 ≠ bundlePreimage E.P d.bundle ∧
        E.P.keccak (claimPreimage E.dec p.2) = bundleHash E.P d.bundle

/-- **(d) HEADLINE: AN ATOMIC LEG TO L1 IS NEITHER RECEIVED ON L1 NOR REFUNDED, OR A LOCATED
COLLISION.** Along any run, for any `Guards`, under `VmCall`, no recoverer at the L1 router's address
on this L2, the publication premise and the run-local decoding premise: for every atomic dispatch
`d` to L1, (1) L1's `bundleStatus` at its bundle hash is `Unreceived`, or the cross-sender salt
clash, or a keccak collision with bytes L1's handler accepted; and (2) its leg is not `Reverted`, or
a keccak collision with the bytes of a logged successful claim. It holds in every reachable state
that meets the premises. That L1 credits a withdrawal only by executing or unbundling its bundle is
argued from source in the Specs header. -/
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

/-- **(b) AND (d) NEED THE PUBLICATION PREMISE.** A pinned run meeting `VmCall`, no recoverer at the
L1 router's address and the decoding premise, in an environment whose inclusion verdict accepts the
bytes of the run's atomic leg to L1 (so `CenterPublishesOnlyPublicDispatches` fails): L1 has executed
that leg (`FullyExecuted`), no public dispatch of the run clashes with it, and every set of bytes
L1's handler accepted has the leg's own bundle-hash preimage. So every disjunct of (b)'s conclusion,
and of (d)'s first conjunct, is false for that leg. -/
def Properties.AtomicToL1StrandedNeedsPublicationPremise : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach pin E (sysInit w₀) S ∧
    VmCall E.sem ∧ NoRecovererAt E.code E.l1Router ∧ DecodesRunBundles E S ∧
    ∃ d ∈ S.src.log, d.isAtomic = true ∧ d.bundle.destinationChainId = E.l1ChainId ∧
      (S.dst E.l1ChainId).status (bundleHash E.P d.bundle) = .FullyExecuted ∧
      (¬ ∃ d' ∈ S.src.log, d'.isAtomic = false ∧ CrossSenderSaltClash E.P d d') ∧
      ∀ x ∈ (S.dst E.l1ChainId).verified, claimPreimage E.dec x = bundlePreimage E.P d.bundle

/-- **(c) AND (d) NEED NO RECOVERER AT THE L1 ROUTER'S ADDRESS.** A pinned run meeting `VmCall`, the
publication premise and the decoding premise, where the code at the L1 router's address on the L2
returns `true` and changes nothing: an atomic leg to L1 has been claimed and is `Reverted`, and every
logged claim's bytes have the leg's own bundle-hash preimage. So (d)'s second conjunct is false for
that leg, and so is (c)'s conclusion for its bytes. -/
def Properties.AtomicToL1StrandedNeedsNoRecoverer : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach pin E (sysInit w₀) S ∧
    VmCall E.sem ∧ CenterPublishesOnlyPublicDispatches E S ∧ DecodesRunBundles E S ∧
    (∃ f, E.code E.l1Router = .recoverer f ∧ ∀ w dest data, f w dest data = some (w, true)) ∧
    ∃ d ∈ S.src.log, d.isAtomic = true ∧ d.bundle.destinationChainId = E.l1ChainId ∧
      S.src.manager.legState d.atomicSend.flowId (bundleHash E.P d.bundle) = .Reverted ∧
      ∀ p ∈ S.claims, claimPreimage E.dec p.2 = bundlePreimage E.P d.bundle

/-! ## (e) `sendMessage` at the pin -/

/-- **(e) COUNTERMODEL: AT THE PIN, A `sendMessage` LEG IS EXECUTED WHILE ITS FLOW IS REFUNDED.** A
run of the pinned code meeting `VmCall`, the publication premise and the decoding premise, in an
environment where no flow gate passes (`finalized` is false everywhere, so every execution is
through `executeBundle`). Two sends carry the `atomicBundle` attribute of the same flow to the same
destination: a `sendMessage`, published and not appended (its leg stays `Unset`), and a
`sendBundle`, appended. Both bundle hashes are legs of the flow. The destination has executed the
first (`FullyExecuted`), and the source has refunded the second (`Reverted`; in the run `authorize`
cites the first leg, which is not appended, and the absence proof is abstracted, Specs header). -/
def Properties.SendMessageAtomicMisrouted : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach pin E (sysInit w₀) S ∧
    VmCall E.sem ∧ CenterPublishesOnlyPublicDispatches E S ∧ DecodesRunBundles E S ∧
    (∀ c h, ¬ E.finalized c h) ∧
    ∃ (s₁ s₂ : Send) (a : AtomicAttr), s₁ ∈ S.sends ∧ s₂ ∈ S.sends ∧
      s₁.entry = .sendMessage ∧ s₂.entry = .sendBundle ∧ s₁.attr = some a ∧ s₂.attr = some a ∧
      s₁.dispatch.isAtomic = false ∧ s₂.dispatch.isAtomic = true ∧ s₁.dest = s₂.dest ∧
      (bundleHash E.P s₁.dispatch.bundle, E.P.chainId) ∈ E.flowLegs a.flowId ∧
      (bundleHash E.P s₂.dispatch.bundle, E.P.chainId) ∈ E.flowLegs a.flowId ∧
      bundleHash E.P s₁.dispatch.bundle ≠ bundleHash E.P s₂.dispatch.bundle ∧
      S.src.manager.legState a.flowId (bundleHash E.P s₁.dispatch.bundle) = .Unset ∧
      (S.dst s₁.dest).status (bundleHash E.P s₁.dispatch.bundle) = .FullyExecuted ∧
      S.src.manager.legState a.flowId (bundleHash E.P s₂.dispatch.bundle) = .Reverted

/-! ## (f) L2 router legs -/

/-- **(f) AN INDIRECT ROUTER CALL TO AN L2 TARGETS THE SOURCE CHAIN'S OWN ROUTER.** Along any run,
for any `Guards`, for every logged send to an L2 and every call formed from an indirect starter
through the L2 router: its `to` and `from` are `L2_ASSET_ROUTER_ADDR`, its data is
`finalizeDeposit(block.chainid, assetId, mintData)` for some asset id and mint data, and the refund
loop's call of it is the code at the router's own address on this chain. -/
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

/-! ## (i) The other tree's checks -/

/-- **(i) WITH BOTH CHECKS OF THE OTHER TREE, THE ATTRIBUTE IS HONOURED OR THE SEND IS REJECTED.**
Along any run of `upgradeTree`, every logged send is atomic exactly when it carried the
`atomicBundle` attribute, and every atomic one goes to a destination whose handler has
`executeAtomicBundle` (in the model, a destination other than L1). -/
def Properties.AttributeHonouredOrRejected : Prop :=
  ∀ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach upgradeTree E (sysInit w₀) S →
    ∀ s ∈ S.sends, (s.dispatch.isAtomic = true ↔ s.attr.isSome = true) ∧
      (s.dispatch.isAtomic = true → atomicEntry (destKind E s.dest) = true)

/-- **WITH THE OTHER TREE'S L1 CHECK, NO ATOMIC LEG GOES TO L1**: along any run of any `Guards`
with `atomicNotToL1`, no logged atomic dispatch has destination L1, so (c) and (d) apply to no
leg. -/
def Properties.GuardKeepsAtomicLegsOffL1 : Prop :=
  ∀ (W : Type) (K : Guards) (E : Env W) (w₀ : W) (S : Sys W), K.atomicNotToL1 = true →
    SysReach K E (sysInit w₀) S →
    ∀ d ∈ S.src.log, d.isAtomic = true → d.bundle.destinationChainId ≠ E.l1ChainId

/-- **AT THE PIN BOTH CONJUNCTS OF (i) FAIL.** A run of the pinned code with a send that carried the
attribute and is not atomic, and an atomic send to a destination without an atomic entry point. -/
def Properties.PinBreaksAttributeHonoured : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach pin E (sysInit w₀) S ∧
    (∃ s ∈ S.sends, s.attr.isSome = true ∧ s.dispatch.isAtomic = false) ∧
    (∃ s ∈ S.sends, s.dispatch.isAtomic = true ∧ atomicEntry (destKind E s.dest) = false)

/-! ## Witnesses -/

/-- **THE PREMISES OF (a)–(d) HOLD ON A PINNED RUN, AND NO COLLISION DISJUNCT DOES.** A run of the
pinned code under `VmCall`, with no recoverer at the L1 router's address, the publication premise
and the decoding premise. It has an atomic dispatch `d` to L1, whose logged send meets
(a)'s premise. The leg's refund has been authorized (the leg is `Revertable`) and L1 has not
received it, while a public withdrawal of the same run is `FullyExecuted` on L1. Every collision
disjunct of (b) and (d) is false. For (c), the leg's own bytes hash to its bundle hash with the same
preimage, so (c)'s collision disjunct is false for them and every claim of them reverts. -/
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
      claimPreimage E.dec (E.P.enc d.bundle) = bundlePreimage E.P d.bundle ∧
      ∀ (st : LegState) (w : W),
        claimRefund (refundStep E (E.P.enc d.bundle)) st w (E.dec (E.P.enc d.bundle)).calls = none

/-- **THE PREMISES OF (g) HOLD.** On the same pinned run, under `VmCall` and the decoding premise:
an atomic leg to an L2 with a call whose target has no recoverer on the source chain, and a call
that, claimed alone, succeeds. Its refund has been authorized (`Revertable`), and no logged claim
hashed to its bundle hash. (In the proof the two calls are a direct call to an address with nothing
deployed on the source chain and a router call.) -/
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

/-- **EVERY CASE OF `AttributeRoutingByEntryPoint` OCCURS.** A pinned run with a `sendMessage`
carrying the attribute (not atomic), a `sendBundle` carrying it (atomic) and a `sendBundle` without
it (not atomic); and an `upgradeTree` run with a `sendMessage` carrying it (atomic), over the same
environment. -/
def Properties.AttributeRoutingByEntryPointWitness : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S S' : Sys W),
    SysReach pin E (sysInit w₀) S ∧ SysReach upgradeTree E (sysInit w₀) S' ∧
    (∃ s ∈ S.sends, s.entry = .sendMessage ∧ s.attr.isSome = true ∧ s.dispatch.isAtomic = false) ∧
    (∃ s ∈ S.sends, s.entry = .sendBundle ∧ s.attr.isSome = true ∧ s.dispatch.isAtomic = true) ∧
    (∃ s ∈ S.sends, s.entry = .sendBundle ∧ s.attr = none ∧ s.dispatch.isAtomic = false) ∧
    (∃ s ∈ S'.sends, s.entry = .sendMessage ∧ s.attr.isSome = true ∧ s.dispatch.isAtomic = true)

/-- **THE PREMISES OF (i) HOLD ON A NONTRIVIAL `upgradeTree` RUN**: an atomic `sendBundle` and an
atomic `sendMessage`, both carrying the attribute, a `sendMessage` that is not atomic, and a send to
L1. -/
def Properties.AttributeHonouredOrRejectedWitness : Prop :=
  ∃ (W : Type) (E : Env W) (w₀ : W) (S : Sys W), SysReach upgradeTree E (sysInit w₀) S ∧
    (∃ s ∈ S.sends, s.entry = .sendBundle ∧ s.dispatch.isAtomic = true ∧ s.attr.isSome = true) ∧
    (∃ s ∈ S.sends, s.entry = .sendMessage ∧ s.dispatch.isAtomic = true ∧ s.attr.isSome = true) ∧
    (∃ s ∈ S.sends, s.entry = .sendMessage ∧ s.dispatch.isAtomic = false) ∧
    (∃ s ∈ S.sends, s.dest = E.l1ChainId)

end Contracts.InteropCenter.AtomicRouting
