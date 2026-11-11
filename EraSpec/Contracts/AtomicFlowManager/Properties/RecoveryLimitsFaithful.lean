import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimitsFaithful

/-!
# Properties: the pinned refund loop calls `InteropCall.to` on the source chain

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimitsFaithful`. Proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsFaithful`.

`AttackVectors.RecoveryLimits` stays true. Its statements are about outcome lists, and
`PinnedClaimSucceedsIffAccepted` shows that the refined loop produces such a list and accepts
exactly when `ClaimAccepted` holds, so Limits 1 and 2 carry over unchanged. What changes is how
Limit 2 should be read. A `reverts` outcome does not only come from a misbehaving implementer.
Every target that runs no code on the source chain produces it (`CodelessTargetReverts`,
`PinnedCallRevertsIff`), and a direct call's target is its recipient on the destination chain
(`FormsCall`). So:

* **Headline.** Take a direct call whose recipient never runs code on the source chain. Every
  claim of its leg reverts, from every leg state and in every world, so no retry helps
  (`DirectCallWithoutSourceCodeBlocksClaim`, from `CodelessTargetBlocksEveryClaim`). The same
  holds for code at that address that never answers a `bool`, such as a twin of the destination
  contract without `recoverAtomicCall` (`NonAnsweringTargetBlocksEveryClaim`). The stateful form
  (`CodelessTargetBlocksClaim`) asks only that the target run no code at the point the loop reaches
  it. All of these are Limit 2 re-proved on the refined loop (`PinnedRevertAnywhereBlocks`).
  The same applies to an indirect call through a sender other than the router (the pin does not
  restrict indirect senders) whose returned recipient exists only on the destination.
* **Countermodel.** The source says a bundle may mix the router's deposit with a flag flip that
  moves no funds and "legitimately return[s] `false`". That reading fails at the pin, on a leg the
  deployed center and manager reach (`FlagFlipDirectCallStrandsDeposit`). The documented outcome
  list `[recovered, declined]` would be accepted. The real list is `[recovered, reverts]`, and the
  deposit is stranded.
* **Strongest true replacement.** A claim succeeds iff the refined outcomes are accepted
  (`PinnedClaimSucceedsIffAccepted`). Success needs code that answers a well-formed `bool` at every
  target (`ClaimSuccessNeedsCodeAtEveryTarget`). Conforming code at every target, one of which
  recovers, is enough (`ConformingTargetsRefund`, witnessed on the same mixed bundle by
  `ConformingTargetsRefundSatisfiable`). So the "mix" design holds exactly for targets that have an
  `IAtomicRecoverable` implementation at the same address on the source chain.
* **L2→L1.** At the pin an atomic withdrawal passes every send-time check
  (`AtomicWithdrawalAdmittedOnlyAtPin`). Its router call targets the L1 router's address, which is
  probed on the source chain, so with no code there its claim reverts
  (`AtomicWithdrawalClaimRevertsWithoutL1RouterCode`, witnessed by `AtomicWithdrawalWitness`).
  Whether such a leg reaches `Revertable` depends on a sibling leg timing out. That route is not
  modelled here.
* **The repair at `e561b9cc2`.** The repaired claim reads the source chain's code at the router
  only (`UpgradeClaimReadsOnlyRouterCode`, made non-trivial by `RepairRemovesTheCodeDependence`).
  It skips a zero-value direct call without calling anything (`UpgradeSkipsZeroValueDirectCalls`),
  refunds the stranded mixed leg (`UpgradeRefundsTheStrandedLeg`), and never recovers toward L1
  (`UpgradeNeverRecoversToL1`).

Every property with premises has a witness that meets them. No property takes a hash premise:
the witnesses never evaluate a bundle hash, and the claim is stated for the bundle presented.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsFaithful

open AttackVectors.RecoveryLimits (Outcome ClaimAccepted)
open Contracts.InteropCenter (Address Word InteropCall Bundle CallStarter Dispatch FormsCall
  FormedBy)

/-! ## One call -/

/-- **AN ACCOUNT THAT RUNS NO CODE RETURNS NO DATA AND CHANGES NOTHING** (`VM-CALL`). -/
def Properties.CodelessCallReturnsNoData : Prop :=
  ∀ (W : Type) (S : SourceChain W) (w : W) (a : Address) (dest : Word) (data : List UInt8),
    S.runsCode w a = false → S.call w a dest data = .returned [] w

/-- **FEWER THAN 32 BYTES DO NOT DECODE AS A `bool`**, so a caller expecting one reverts. -/
def Properties.ShortReturnDataDoesNotDecode : Prop :=
  ∀ rd : List UInt8, rd.length < 32 → decodeBool rd = none

/-- **A WELL-FORMED `bool` DECODES, WHATEVER FOLLOWS IT.** -/
def Properties.AbiBoolDecodes : Prop :=
  ∀ (b : Bool) (rest : List UInt8), decodeBool (abiBool b ++ rest) = some b

/-- **A TARGET THAT RUNS NO CODE ON THE SOURCE CHAIN REVERTS.** Its outcome is `reverts`, not
`declined`, and the outcome list stops there. -/
def Properties.CodelessTargetReverts : Prop :=
  ∀ (W : Type) (S : SourceChain W) (dest : Word) (w : W) (c : InteropCall) (cs : List InteropCall),
    S.runsCode w c.target = false →
      pinnedProbe S dest w c = none ∧ outcomes (pinnedProbe S dest) w (c :: cs) = [Outcome.reverts]

/-- **EXACTLY WHEN ONE CALL REVERTS.** The pinned call of `c.to` reverts iff the target runs no
code, or its code returns nothing that decodes as a `bool`, which includes reverting. This
replaces Limit 2's "a target that REVERTS rather than returning `false`". -/
def Properties.PinnedCallRevertsIff : Prop :=
  ∀ (W : Type) (S : SourceChain W) (dest : Word) (w : W) (c : InteropCall),
    pinnedProbe S dest w c = none ↔
      (S.runsCode w c.target = false ∨
        ∀ rd w', S.exec w c.target dest c.data = .returned rd w' → decodeBool rd = none)

/-! ## The loop is `RecoveryLimits`' acceptance rule -/

/-- **THE REFINED LOOP ACCEPTS EXACTLY WHEN `ClaimAccepted` HOLDS.** For every source chain, a
claim on a `Revertable` leg succeeds exactly when the outcomes the loop produces on the threaded
world satisfy `AttackVectors.RecoveryLimits.ClaimAccepted`: no call reverted, and at least one
recovered. So every result of that file applies to these outcome lists. -/
def Properties.PinnedClaimSucceedsIffAccepted : Prop :=
  ∀ (W : Type) (S : SourceChain W) (w : W) (b : Bundle),
    (claimRefundPinned S .Revertable w b).isSome = true ↔
      ClaimAccepted (outcomes (pinnedProbe S b.destinationChainId) w b.calls)

/-- **LIMIT 2, RE-PROVED ON THE REFINED LOOP.** Take a call that reverts in every world the
earlier calls can leave. Wherever it sits in the bundle, it blocks the claim, from every leg state.
Witnessed by `CodelessTargetBlocksClaimWitness`. -/
def Properties.PinnedRevertAnywhereBlocks : Prop :=
  ∀ (W : Type) (S : SourceChain W) (s : LegState) (w : W) (b : Bundle)
    (pre post : List InteropCall) (c : InteropCall),
    b.calls = pre ++ c :: post →
    (∀ w' n, recoverLoop (pinnedProbe S b.destinationChainId) w pre = some (w', n) →
      pinnedProbe S b.destinationChainId w' c = none) →
      claimRefundPinned S s w b = none

/-! ## A target with no code on the source chain blocks the claim -/

/-- **A TARGET THAT RUNS NO CODE WHERE THE LOOP REACHES IT BLOCKS THE CLAIM.** The premise is
evaluated on the world the earlier calls actually leave, so it allows code to appear or disappear
before. Witnessed by `CodelessTargetBlocksClaimWitness`. -/
def Properties.CodelessTargetBlocksClaim : Prop :=
  ∀ (W : Type) (S : SourceChain W) (s : LegState) (w : W) (b : Bundle)
    (pre post : List InteropCall) (c : InteropCall),
    b.calls = pre ++ c :: post →
    (∀ w' n, recoverLoop (pinnedProbe S b.destinationChainId) w pre = some (w', n) →
      S.runsCode w' c.target = false) →
      claimRefundPinned S s w b = none

/-- **THE STATEFUL PREMISES ARE MET, NOT VACUOUSLY.** On the mixed bundle, the call before the flag
flip completes and recovers: the loop over it is `some ((), 1)`, so the premise is not discharged
by an earlier revert. The flag contract runs no code in the world that call leaves, so its call
reverts there. -/
def Properties.CodelessTargetBlocksClaimWitness : Prop :=
  mixD.bundle.calls = [wRouterCall] ++ wFlagCall :: []
  ∧ recoverLoop (pinnedProbe wSource mixD.bundle.destinationChainId) () [wRouterCall] = some ((), 1)
  ∧ (∀ w' n, recoverLoop (pinnedProbe wSource mixD.bundle.destinationChainId) () [wRouterCall]
      = some (w', n) → wSource.runsCode w' wFlagCall.target = false)
  ∧ pinnedProbe wSource mixD.bundle.destinationChainId () wFlagCall = none

/-- **A TARGET THAT NEVER ANSWERS BLOCKS EVERY CLAIM, FOR GOOD.** Suppose that in every world the
call of `c.to` reverts or returns nothing that decodes as a `bool` (`PinnedCallRevertsIff`). Then
every attempt to claim the bundle reverts, from every leg state and in every world. A reverted
claim leaves the leg `Revertable` (`claimRefundPinned` is `none`), so the leg can be retried
forever and is never refunded. This covers a destination contract's twin deployed at the same
address on the source chain without `recoverAtomicCall`. Witnessed by
`FlagFlipDirectCallStrandsDeposit`. -/
def Properties.NonAnsweringTargetBlocksEveryClaim : Prop :=
  ∀ (W : Type) (S : SourceChain W) (b : Bundle) (c : InteropCall),
    c ∈ b.calls → (∀ w, pinnedProbe S b.destinationChainId w c = none) →
      ∀ (s : LegState) (w : W), claimRefundPinned S s w b = none

/-- **…SO ONE THAT NEVER RUNS CODE BLOCKS EVERY CLAIM, FOR GOOD.** The case of an EOA, or of an
address only the destination chain deployed to. Witnessed by `FlagFlipDirectCallStrandsDeposit`. -/
def Properties.CodelessTargetBlocksEveryClaim : Prop :=
  ∀ (W : Type) (S : SourceChain W) (b : Bundle) (c : InteropCall),
    c ∈ b.calls → NeverRunsCode S c.target →
      ∀ (s : LegState) (w : W), claimRefundPinned S s w b = none

/-- **HEADLINE: A DIRECT CALL WHOSE RECIPIENT HAS NO CODE ON THE SOURCE CHAIN MAKES ITS LEG
UNREFUNDABLE.** Take a dispatch the center formed (`FormedBy`) with a direct call starter. If the
starter's recipient never runs code on the source chain, every `claimRefund` of the leg's bundle
reverts, from every leg state and in every world. That covers the zero-value flag flips
`_validateAtomicBundle` admits, and the router deposits in the same bundle, which are stranded
with it. Witnessed by `FlagFlipDirectCallStrandsDeposit`, on a leg the deployed center and manager
reach. -/
def Properties.DirectCallWithoutSourceCodeBlocksClaim : Prop :=
  ∀ (P : Contracts.InteropCenter.Params) (d : Dispatch) (cs : CallStarter) (W : Type)
    (S : SourceChain W),
    FormedBy P d → cs ∈ d.starters → cs.callAttributes.indirectCall = false →
    NeverRunsCode S cs.target →
      ∀ (s : LegState) (w : W), claimRefundPinned S s w d.bundle = none

/-! ## What a successful claim needs, and what suffices -/

/-- **A SUCCESSFUL CLAIM NEEDS CODE ANSWERING A `bool` AT EVERY TARGET.** If the claim succeeds,
then for every call some world of the source chain ran code at `c.to`, and that code returned data
that decodes as a `bool`. -/
def Properties.ClaimSuccessNeedsCodeAtEveryTarget : Prop :=
  ∀ (W : Type) (S : SourceChain W) (s : LegState) (w : W) (b : Bundle) (r : LegState × W),
    claimRefundPinned S s w b = some r →
      ∀ c ∈ b.calls, ∃ w' : W, S.runsCode w' c.target = true ∧
        ∃ rd w'', S.exec w' c.target b.destinationChainId c.data = .returned rd w'' ∧
          decodeBool rd ≠ none

/-- **CONFORMING CODE AT EVERY TARGET, ONE OF WHICH RECOVERS, IS ENOUGH.** If every target runs
code that answers every call with a well-formed `bool`, and one call's target always recovers it,
the claim of a `Revertable` leg succeeds. Witnessed by `ConformingTargetsRefundSatisfiable`. -/
def Properties.ConformingTargetsRefund : Prop :=
  ∀ (W : Type) (S : SourceChain W) (w : W) (b : Bundle) (c : InteropCall),
    (∀ c' ∈ b.calls, Conforms S c'.target) → c ∈ b.calls →
    AlwaysRecovers S c.target b.destinationChainId c.data →
      ∃ w', claimRefundPinned S .Revertable w b = some (.Reverted, w')

/-- **THE CONFORMING PREMISE IS SATISFIABLE, ON THE MIXED BUNDLE.** With a conforming contract at
`5` on the source chain that answers `false`, the mixed bundle's claim succeeds on the outcomes
`[recovered, declined]`. Only the source chain changed: the bundle is the stranded one of
`FlagFlipDirectCallStrandsDeposit`. -/
def Properties.ConformingTargetsRefundSatisfiable : Prop :=
  (∀ c' ∈ mixD.bundle.calls, Conforms wSourceConforming c'.target)
  ∧ wRouterCall ∈ mixD.bundle.calls
  ∧ AlwaysRecovers wSourceConforming wRouterCall.target mixD.bundle.destinationChainId
      wRouterCall.data
  ∧ outcomes (pinnedProbe wSourceConforming mixD.bundle.destinationChainId) () mixD.bundle.calls
      = [Outcome.recovered, Outcome.declined]
  ∧ claimRefundPinned wSourceConforming .Revertable () mixD.bundle = some (.Reverted, ())

/-! ## Countermodel: the documented "mix" reading fails at the pin -/

/-- **COUNTERMODEL: A FLAG FLIP STRANDS THE DEPOSIT IT IS BUNDLED WITH.** The deployed center and
manager reach a state in which the mixed leg is `Revertable`. The center formed the leg from a
router call and a zero-value direct call, and it passes `_validateAtomicBundle`. On the source
chain the router conforms and recovers its deposit, and the flag contract has no code. The
documented reading (`AtomicFlowManager.sol:208-211`, `IAtomicRecoverable.sol:13-15`,
`InteropCenter.sol:663-665`) gives the flag flip `declined`, and its outcome list would be accepted.
The pinned code gives `reverts`, and every claim of the leg reverts, so the deposit is never
refunded. -/
def Properties.FlagFlipDirectCallStrandsDeposit : Prop :=
  Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      Contracts.InteropCenter.init mixS2
  ∧ mixS2.manager.legState mixD.atomicSend.flowId
      (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle) = .Revertable
  ∧ FormedBy Contracts.InteropCenter.wParams mixD
  ∧ Contracts.InteropCenter.wDirect 0 ∈ mixD.starters
  ∧ (Contracts.InteropCenter.wDirect 0).callAttributes.indirectCall = false
  ∧ Contracts.InteropCenter.Validated mixD.bundle
  ∧ Conforms wSource wRouterCall.target
  ∧ AlwaysRecovers wSource wRouterCall.target mixD.bundle.destinationChainId wRouterCall.data
  ∧ NeverRunsCode wSource (Contracts.InteropCenter.wDirect 0).target
  ∧ ClaimAccepted [Outcome.recovered, Outcome.declined]
  ∧ outcomes (pinnedProbe wSource mixD.bundle.destinationChainId) () mixD.bundle.calls
      = [Outcome.recovered, Outcome.reverts]
  ∧ ∀ (s : LegState) (w : Unit), claimRefundPinned wSource s w mixD.bundle = none

/-! ## L2→L1: the router's call targets the L1 router's address -/

/-- **AT THE PIN AN ATOMIC WITHDRAWAL IS ADMITTED; AT `e561b9cc2` IT IS NOT.** A single indirect,
zero-value starter through the L2 asset router passes the pinned L1-destination checks. The call
the router forms has `to` the L1 router's address and zero value, so it passes
`_validateAtomicBundle`. The repaired center rejects an atomic bundle to L1. -/
def Properties.AtomicWithdrawalAdmittedOnlyAtPin : Prop :=
  ∀ (l1ChainId : Word) (l1AssetRouter l2AssetRouter sender : Address) (data : List UInt8)
    (cs : CallStarter),
    cs.target = l2AssetRouter → cs.callAttributes.indirectCall = true →
    cs.callAttributes.interopCallValue = 0 →
      PinnedL1SendChecks l1ChainId l2AssetRouter l1ChainId [cs]
      ∧ FormsCall sender cs ⟨routerIndirectRecipient l1ChainId l1AssetRouter l2AssetRouter
          l1ChainId, l2AssetRouter, 0, data⟩
      ∧ routerIndirectRecipient l1ChainId l1AssetRouter l2AssetRouter l1ChainId = l1AssetRouter
      ∧ (∀ b : Bundle, b.calls = [⟨routerIndirectRecipient l1ChainId l1AssetRouter l2AssetRouter
          l1ChainId, l2AssetRouter, 0, data⟩] → Contracts.InteropCenter.Validated b)
      ∧ ¬ UpgradeDestinationCheck l1ChainId l1ChainId true

/-- **AN ATOMIC WITHDRAWAL'S CLAIM REVERTS IF THE L1 ROUTER'S ADDRESS RUNS NO CODE ON THE SOURCE
CHAIN.** The router's call in an L1-destined bundle targets `L1_ASSET_ROUTER`, which the pinned
loop calls on the source L2. Witnessed by `AtomicWithdrawalWitness`. -/
def Properties.AtomicWithdrawalClaimRevertsWithoutL1RouterCode : Prop :=
  ∀ (l1ChainId : Word) (l1AssetRouter l2AssetRouter : Address) (W : Type) (S : SourceChain W)
    (b : Bundle) (c : InteropCall),
    b.destinationChainId = l1ChainId → c ∈ b.calls →
    c.target = routerIndirectRecipient l1ChainId l1AssetRouter l2AssetRouter b.destinationChainId →
    NeverRunsCode S l1AssetRouter →
      ∀ (s : LegState) (w : W), claimRefundPinned S s w b = none

/-- **THE WITHDRAWAL PREMISES ARE SATISFIABLE.** The witness withdrawal passes the pinned checks,
its bundle targets the L1 router `11`, which runs no code on `wSource`, and every claim reverts.
The repaired center would have rejected the send. -/
def Properties.AtomicWithdrawalWitness : Prop :=
  PinnedL1SendChecks wL1 9 wL1 [Contracts.InteropCenter.wIndirect]
  ∧ FormsCall 1 Contracts.InteropCenter.wIndirect wWithdrawCall
  ∧ Contracts.InteropCenter.Validated wWithdrawBundle
  ∧ wWithdrawBundle.destinationChainId = wL1
  ∧ wWithdrawCall ∈ wWithdrawBundle.calls
  ∧ wWithdrawCall.target = routerIndirectRecipient wL1 wL1Router 9 wWithdrawBundle.destinationChainId
  ∧ NeverRunsCode wSource wL1Router
  ∧ (∀ (s : LegState) (w : Unit), claimRefundPinned wSource s w wWithdrawBundle = none)
  ∧ ¬ UpgradeDestinationCheck wL1 wWithdrawBundle.destinationChainId true

/-! ## The repair at e561b9cc2 -/

/-- **THE REPAIRED CLAIM READS THE SOURCE CHAIN'S CODE AT THE ROUTER ONLY.** Two source chains
that agree at the router give the same repaired claim, whatever runs at any other address. That
includes a direct call's recipient and its sender. -/
def Properties.UpgradeClaimReadsOnlyRouterCode : Prop :=
  ∀ (W : Type) (S S' : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (s : LegState) (w : W) (b : Bundle),
    (∀ w, S.runsCode w router = S'.runsCode w router) →
    (∀ w dest data, S.exec w router dest data = S'.exec w router dest data) →
      claimRefundUpgrade S router l1ChainId baseRecover s w b
        = claimRefundUpgrade S' router l1ChainId baseRecover s w b

/-- **THE REPAIRED LOOP SKIPS A ZERO-VALUE DIRECT CALL WITHOUT CALLING ANYTHING.** -/
def Properties.UpgradeSkipsZeroValueDirectCalls : Prop :=
  ∀ (W : Type) (S : SourceChain W) (router : Address)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (dest baseAsset : Word) (w : W)
    (c : InteropCall),
    c.fromAddr ≠ router → c.value = 0 → upgradeStep S router baseRecover dest baseAsset w c = some w

/-- **THE REPAIR REMOVES THE DEPENDENCE, ON THE WITNESS.** `wSource` and `wSourceConforming` agree
at the router and differ at the flag contract `5`. The pinned claims of the mixed leg differ,
while the repaired claims agree. -/
def Properties.RepairRemovesTheCodeDependence : Prop :=
  (∀ w, wSource.runsCode w 9 = wSourceConforming.runsCode w 9)
  ∧ (∀ w dest data, wSource.exec w 9 dest data = wSourceConforming.exec w 9 dest data)
  ∧ wSource.runsCode () 5 ≠ wSourceConforming.runsCode () 5
  ∧ claimRefundPinned wSource .Revertable () mixD.bundle
      ≠ claimRefundPinned wSourceConforming .Revertable () mixD.bundle
  ∧ ∀ baseRecover : Unit → Word → Word → Address → ℕ → Option Unit,
      claimRefundUpgrade wSource 9 wL1 baseRecover .Revertable () mixD.bundle
        = claimRefundUpgrade wSourceConforming 9 wL1 baseRecover .Revertable () mixD.bundle

/-- **THE REPAIRED CLAIM REFUNDS THE STRANDED MIXED LEG**, on the source chain where the pinned
claim always reverts, whatever the router's base-token refund would do. The mixed bundle carries
no value, so that refund is never called. -/
def Properties.UpgradeRefundsTheStrandedLeg : Prop :=
  ∀ baseRecover : Unit → Word → Word → Address → ℕ → Option Unit,
    claimRefundUpgrade wSource 9 wL1 baseRecover .Revertable () mixD.bundle = some (.Reverted, ())

/-- **THE REPAIRED CLAIM NEVER RECOVERS TOWARD L1** (`RecoverToL1NotSupported`). With
`AtomicBundleToL1NotSupported` at send time, no such leg exists to claim. -/
def Properties.UpgradeNeverRecoversToL1 : Prop :=
  ∀ (W : Type) (S : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (s : LegState) (w : W) (b : Bundle),
    b.destinationChainId = l1ChainId → claimRefundUpgrade S router l1ChainId baseRecover s w b = none

end Contracts.AtomicFlowManager.RecoveryLimitsFaithful
