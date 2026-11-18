import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimitsFaithful

/-!
# Properties: the refund loop's external call, at the pin and at `draft/v0.35.0`

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimitsFaithful`. Proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsFaithful`.

* **One call.** A call to an account that runs no code returns no data and changes nothing
  (`CodelessCallReturnsNoData`). Fewer than 32 bytes do not decode as a `bool`
  (`ShortReturnDataDoesNotDecode`), and a well-formed `bool` decodes whatever follows it
  (`AbiBoolDecodes`). So the pinned call of `c.to` reverts in a world exactly when, in that world,
  `c.to` runs no code or its code returns nothing that decodes as a `bool` (`PinnedCallRevertsIff`,
  `CodelessTargetReverts`).
* **The loop is `RecoveryLimits`' acceptance rule.** A claim of a `Revertable` leg succeeds exactly
  when the outcome list the loop produces on the threaded world satisfies
  `AttackVectors.RecoveryLimits.ClaimAccepted` (`PinnedClaimSucceedsIffAccepted`). A successful
  claim is a `claim` step of the manager model (`PinnedClaimIsAManagerClaimStep`). Limit 2 holds on
  the threaded world (`PinnedRevertAnywhereBlocks`).
* **A target that runs no code.** If a call's target runs no code in the world in which the loop
  reaches it, the claim reverts (`CodelessTargetBlocksClaim`). If a target never runs code, or
  never answers a `bool`, the claim reverts from every leg state and in every world
  (`CodelessTargetBlocksEveryClaim`, `NonAnsweringTargetBlocksEveryClaim`). In a bundle the center
  formed, a direct call's target is its starter's recipient, so the same holds for a direct
  starter whose recipient never runs code on the source chain
  (`DirectCallWithoutSourceCodeBlocksClaim`).
* **What a successful claim needs, and what suffices.** Success needs, for every call, code at its
  target that returned a decodable `bool` in some world (`ClaimSuccessNeedsCodeAtEveryTarget`).
  Conforming code at every target, one of which always recovers its call, suffices
  (`ConformingTargetsRefund`).
* **The loop at `draft/v0.35.0`.** The claim reads the source chain's code at the router only
  (`V35ClaimReadsOnlyRouterCode`), calls nothing for a zero-value call whose `from` is not the
  router (`V35SkipsZeroValueNonRouterCalls`), succeeds when the router conforms and the base-token
  refund does not revert (`V35ClaimSucceedsWithConformingRouter`), and rejects an L1 destination
  (`V35ClaimRejectsL1Destination`).

The witnesses use one two-call leg, the router's deposit call and a zero-value direct call to
contract `5`, which the deployed center and manager of `Contracts.InteropCenter` bring to
`Revertable`. Three source chains differ only in the code at `5`: none
(`DirectCallWithoutSourceCodeBlocksClaimWitness`), code without `recoverAtomicCall`
(`NonAnsweringTargetWitness`), and code that answers `false`
(`ConformingTargetsRefundSatisfiable`, `PinnedClaimStepWitness`). On that bundle the pinned claim
depends on the code at `5` and the `draft/v0.35.0` claim does not
(`DirectTargetCodeDecidesOnlyThePinnedClaim`, `V35ClaimSucceedsOnMixedBundle`).
`V35ClaimWitness` has a direct call that carries value.

Every property with premises has a witness that meets them. No property takes a hash premise:
the claim is stated for the bundle presented.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsFaithful

open AttackVectors.RecoveryLimits (Outcome ClaimAccepted)
open Contracts.InteropCenter (Address Word InteropCall Bundle CallStarter Dispatch FormsCall
  FormedBy)

/-! ## One call -/

/-- **AN ACCOUNT THAT RUNS NO CODE RETURNS NO DATA AND CHANGES NOTHING** (`VM-CALL`). Witnessed by
`DecodeBoolWitness`. -/
def Properties.CodelessCallReturnsNoData : Prop :=
  ∀ (W : Type) (S : SourceChain W) (w : W) (a : Address) (dest : Word) (data : List UInt8),
    S.runsCode w a = false → S.call w a dest data = .returned [] w

/-- **FEWER THAN 32 BYTES DO NOT DECODE AS A `bool`**, so a caller expecting one reverts. Witnessed
by `DecodeBoolWitness`. -/
def Properties.ShortReturnDataDoesNotDecode : Prop :=
  ∀ rd : List UInt8, rd.length < 32 → decodeBool rd = none

/-- **A WELL-FORMED `bool` DECODES, WHATEVER FOLLOWS IT.** -/
def Properties.AbiBoolDecodes : Prop :=
  ∀ (b : Bool) (rest : List UInt8), decodeBool (abiBool b ++ rest) = some b

/-- **THE DECODER'S PREMISES ARE MET.** On `wSource` the account `5` runs no code, and the call of
`recoverAtomicCall` on it returns the empty return data, which is shorter than 32 bytes and does
not decode. A 32-byte word other than `0` or `1` does not decode either, and a `true` word followed
by one more byte decodes as `true`. -/
def Properties.DecodeBoolWitness : Prop :=
  wSource.runsCode () 5 = false
  ∧ wSource.call () 5 325 [] = .returned [] ()
  ∧ ([] : List UInt8).length < 32
  ∧ decodeBool [] = none
  ∧ decodeBool (List.replicate 32 7) = none
  ∧ decodeBool (abiBool true ++ [7]) = some true

/-- **A TARGET THAT RUNS NO CODE REVERTS THE CALL.** Its outcome is `reverts`, not `declined`, and
the outcome list stops there. Witnessed by `DirectCallWithoutSourceCodeBlocksClaimWitness`. -/
def Properties.CodelessTargetReverts : Prop :=
  ∀ (W : Type) (S : SourceChain W) (dest : Word) (w : W) (c : InteropCall) (cs : List InteropCall),
    S.runsCode w c.target = false →
      pinnedProbe S dest w c = none ∧ outcomes (pinnedProbe S dest) w (c :: cs) = [Outcome.reverts]

/-- **EXACTLY WHEN ONE CALL REVERTS.** The pinned call of `c.to` reverts iff the target runs no
code, or its code returns nothing that decodes as a `bool`, which includes reverting. -/
def Properties.PinnedCallRevertsIff : Prop :=
  ∀ (W : Type) (S : SourceChain W) (dest : Word) (w : W) (c : InteropCall),
    pinnedProbe S dest w c = none ↔
      (S.runsCode w c.target = false ∨
        ∀ rd w', S.exec w c.target dest c.data = .returned rd w' → decodeBool rd = none)

/-! ## The loop is `RecoveryLimits`' acceptance rule -/

/-- **THE LOOP ACCEPTS EXACTLY WHEN `ClaimAccepted` HOLDS.** For every source chain, a claim on a
`Revertable` leg succeeds exactly when the outcomes the loop produces on the threaded world satisfy
`AttackVectors.RecoveryLimits.ClaimAccepted`: no call reverted, and at least one recovered. So
every result of that file applies to these outcome lists. -/
def Properties.PinnedClaimSucceedsIffAccepted : Prop :=
  ∀ (W : Type) (S : SourceChain W) (w : W) (b : Bundle),
    (claimRefundPinned S .Revertable w b).isSome = true ↔
      ClaimAccepted (outcomes (pinnedProbe S b.destinationChainId) w b.calls)

/-- **A SUCCESSFUL CLAIM IS A `claim` STEP OF THE MANAGER MODEL.** Run on the state of leg
`(f, h)` of a manager state `M`, a successful pinned claim found that leg `Revertable` and leaves it
`Reverted`, and writing that state back is `Contracts.AtomicFlowManager.Step.claim`. This is a gate
lemma: `claimRefundPinned` succeeds only from `Revertable`, which is exactly `Step.claim`'s guard,
so it ties the two models together and adds little beyond that gate. `h` is the key
the claim reads; which key a presented bundle hashes to is not modelled here. Witnessed by
`PinnedClaimStepWitness`. -/
def Properties.PinnedClaimIsAManagerClaimStep : Prop :=
  ∀ (W : Type) (S : SourceChain W) (M : Contracts.AtomicFlowManager.Manager) (f h : Word) (w : W)
    (b : Bundle) (r : LegState × W),
    claimRefundPinned S (M.legState f h) w b = some r →
      M.legState f h = .Revertable ∧ r.1 = .Reverted
      ∧ Contracts.AtomicFlowManager.Step M (M.set f h r.1)

/-- **LIMIT 2 ON THE THREADED WORLD.** Take a call that reverts in every world the calls before it
can leave. Wherever it sits in the bundle, every claim reverts, from every leg state. Witnessed by
`CodelessTargetBlocksClaimWitness`. -/
def Properties.PinnedRevertAnywhereBlocks : Prop :=
  ∀ (W : Type) (S : SourceChain W) (s : LegState) (w : W) (b : Bundle)
    (pre post : List InteropCall) (c : InteropCall),
    b.calls = pre ++ c :: post →
    (∀ w' n, recoverLoop (pinnedProbe S b.destinationChainId) w pre = some (w', n) →
      pinnedProbe S b.destinationChainId w' c = none) →
      claimRefundPinned S s w b = none

/-! ## A target that runs no code -/

/-- **A TARGET THAT RUNS NO CODE WHERE THE LOOP REACHES IT MAKES THE CLAIM REVERT.** The premise is
evaluated on the world the earlier calls actually leave, so it allows code to appear or disappear
before. Witnessed by `CodelessTargetBlocksClaimWitness`. -/
def Properties.CodelessTargetBlocksClaim : Prop :=
  ∀ (W : Type) (S : SourceChain W) (s : LegState) (w : W) (b : Bundle)
    (pre post : List InteropCall) (c : InteropCall),
    b.calls = pre ++ c :: post →
    (∀ w' n, recoverLoop (pinnedProbe S b.destinationChainId) w pre = some (w', n) →
      S.runsCode w' c.target = false) →
      claimRefundPinned S s w b = none

/-- **THE STATEFUL PREMISES ARE MET, NOT VACUOUSLY.** On the two-call bundle, the call before the
direct call completes and recovers: the loop over it is `some ((), 1)`, so the premise is not
discharged by an earlier revert. The direct call's target runs no code in the world that call
leaves, so the direct call reverts there. -/
def Properties.CodelessTargetBlocksClaimWitness : Prop :=
  mixD.bundle.calls = [wRouterCall] ++ wDirectCall :: []
  ∧ recoverLoop (pinnedProbe wSource mixD.bundle.destinationChainId) () [wRouterCall] = some ((), 1)
  ∧ (∀ w' n, recoverLoop (pinnedProbe wSource mixD.bundle.destinationChainId) () [wRouterCall]
      = some (w', n) → wSource.runsCode w' wDirectCall.target = false)
  ∧ pinnedProbe wSource mixD.bundle.destinationChainId () wDirectCall = none

/-- **A TARGET THAT NEVER ANSWERS A `bool` MAKES EVERY CLAIM REVERT.** Suppose that in every world
the call of `c.to` reverts or returns nothing that decodes as a `bool` (`PinnedCallRevertsIff`).
Then every claim of the bundle reverts, from every leg state and in every world. A reverted claim
leaves the leg's state as it was (`claimRefundPinned` is `none`). This covers code at `c.to` that
has no `recoverAtomicCall`. Witnessed by `NonAnsweringTargetWitness`. -/
def Properties.NonAnsweringTargetBlocksEveryClaim : Prop :=
  ∀ (W : Type) (S : SourceChain W) (b : Bundle) (c : InteropCall),
    c ∈ b.calls → (∀ w, pinnedProbe S b.destinationChainId w c = none) →
      ∀ (s : LegState) (w : W), claimRefundPinned S s w b = none

/-- **THE NON-ANSWERING PREMISE IS MET BY CODE THAT RUNS.** On `wSourceNoHook`, code runs at `5`
and reverts on `recoverAtomicCall`. The direct call of the two-call bundle then reverts in every
world, and every claim of the bundle reverts. -/
def Properties.NonAnsweringTargetWitness : Prop :=
  wSourceNoHook.runsCode () 5 = true
  ∧ wDirectCall ∈ mixD.bundle.calls
  ∧ (∀ w, pinnedProbe wSourceNoHook mixD.bundle.destinationChainId w wDirectCall = none)
  ∧ ∀ (s : LegState) (w : Unit), claimRefundPinned wSourceNoHook s w mixD.bundle = none

/-- **A TARGET THAT NEVER RUNS CODE MAKES EVERY CLAIM REVERT.** The case of an EOA, or of an address
with nothing deployed on the source chain. Witnessed by
`DirectCallWithoutSourceCodeBlocksClaimWitness`. -/
def Properties.CodelessTargetBlocksEveryClaim : Prop :=
  ∀ (W : Type) (S : SourceChain W) (b : Bundle) (c : InteropCall),
    c ∈ b.calls → NeverRunsCode S c.target →
      ∀ (s : LegState) (w : W), claimRefundPinned S s w b = none

/-- **A DIRECT STARTER WHOSE RECIPIENT NEVER RUNS CODE ON THE SOURCE CHAIN.** Take a dispatch the
center formed (`FormedBy`) with a direct call starter. If the starter's recipient never runs code
on the source chain, every pinned `claimRefund` of the dispatch's bundle reverts, from every leg
state and in every world. Witnessed by `DirectCallWithoutSourceCodeBlocksClaimWitness`. -/
def Properties.DirectCallWithoutSourceCodeBlocksClaim : Prop :=
  ∀ (P : Contracts.InteropCenter.Params) (d : Dispatch) (cs : CallStarter) (W : Type)
    (S : SourceChain W),
    FormedBy P d → cs ∈ d.starters → cs.callAttributes.indirectCall = false →
    NeverRunsCode S cs.target →
      ∀ (s : LegState) (w : W), claimRefundPinned S s w d.bundle = none

/-- **THE DIRECT-CALL PREMISES ARE MET ON A LEG THE DEPLOYED CENTER REACHES.** The deployed center
and manager of `Contracts.InteropCenter`'s model, whose `authorize` omits the proof checks of
`authorizeRefund`, reach a state in which the two-call leg is `Revertable`. The center formed the
leg from the router's indirect starter and a direct starter with value `0`, and it passes
`_validateAtomicBundle`. On `wSource` the direct starter's recipient never runs code; the router
call recovers and the direct call reverts, and every claim of the leg's bundle reverts. -/
def Properties.DirectCallWithoutSourceCodeBlocksClaimWitness : Prop :=
  Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      Contracts.InteropCenter.init mixS2
  ∧ mixS2.manager.legState mixD.atomicSend.flowId
      (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle) = .Revertable
  ∧ FormedBy Contracts.InteropCenter.wParams mixD
  ∧ Contracts.InteropCenter.wDirect 0 ∈ mixD.starters
  ∧ (Contracts.InteropCenter.wDirect 0).callAttributes.indirectCall = false
  ∧ Contracts.InteropCenter.Validated mixD.bundle
  ∧ NeverRunsCode wSource (Contracts.InteropCenter.wDirect 0).target
  ∧ wDirectCall ∈ mixD.bundle.calls
  ∧ wDirectCall.target = (Contracts.InteropCenter.wDirect 0).target
  ∧ wSource.runsCode () wDirectCall.target = false
  ∧ outcomes (pinnedProbe wSource mixD.bundle.destinationChainId) () mixD.bundle.calls
      = [Outcome.recovered, Outcome.reverts]
  ∧ ∀ (s : LegState) (w : Unit), claimRefundPinned wSource s w mixD.bundle = none

/-! ## What a successful claim needs, and what suffices -/

/-- **A SUCCESSFUL CLAIM NEEDS CODE ANSWERING A `bool` AT EVERY TARGET.** If the claim succeeds,
then for every call some world of the source chain ran code at `c.to`, and that code returned data
that decodes as a `bool`. Witnessed by `ConformingTargetsRefundSatisfiable`. -/
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

/-- **THE CONFORMING PREMISES ARE MET ON THE TWO-CALL BUNDLE.** With code at `5` on the source
chain that answers `false`, both targets conform, the router always recovers its call, and the
two-call bundle's claim succeeds on the outcomes `[recovered, declined]`. -/
def Properties.ConformingTargetsRefundSatisfiable : Prop :=
  (∀ c' ∈ mixD.bundle.calls, Conforms wSourceConforming c'.target)
  ∧ wRouterCall ∈ mixD.bundle.calls
  ∧ AlwaysRecovers wSourceConforming wRouterCall.target mixD.bundle.destinationChainId
      wRouterCall.data
  ∧ outcomes (pinnedProbe wSourceConforming mixD.bundle.destinationChainId) () mixD.bundle.calls
      = [Outcome.recovered, Outcome.declined]
  ∧ claimRefundPinned wSourceConforming .Revertable () mixD.bundle = some (.Reverted, ())

/-- **THE CLAIM STEP ON THE CENTER'S RUN.** On `wSourceConforming`, the pinned claim run on the
two-call leg's state in `mixS2` succeeds. Writing its state back to the leg is a step of the
deployed center model, so the deployed center and manager reach a state in which that leg is
`Reverted`. -/
def Properties.PinnedClaimStepWitness : Prop :=
  claimRefundPinned wSourceConforming
      (mixS2.manager.legState 7
        (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle))
      () mixD.bundle = some (.Reverted, ())
  ∧ Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      Contracts.InteropCenter.init
      { mixS2 with
        manager := mixS2.manager.set 7
          (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle)
          .Reverted }

/-! ## The loop at `draft/v0.35.0` (b17415d) -/

/-- **THE `draft/v0.35.0` CLAIM READS THE SOURCE CHAIN'S CODE AT THE ROUTER ONLY.** Two source
chains that agree at the router give the same claim, whatever the source-chain parameter `S` runs
at any other address. That includes every call's `to`, and the `from` of every call not sent by the
router. The base-token refund step `baseRecover` is held fixed: in the contract it calls further
contracts (the base token, the asset tracker), and this statement says nothing about them. The
independence from `S` off the router holds by how `v35Step` is built. Witnessed by
`DirectTargetCodeDecidesOnlyThePinnedClaim`. -/
def Properties.V35ClaimReadsOnlyRouterCode : Prop :=
  ∀ (W : Type) (S S' : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (s : LegState) (w : W) (b : Bundle),
    (∀ w, S.runsCode w router = S'.runsCode w router) →
    (∀ w dest data, S.exec w router dest data = S'.exec w router dest data) →
      claimRefundV35 S router l1ChainId baseRecover s w b
        = claimRefundV35 S' router l1ChainId baseRecover s w b

/-- **A ZERO-VALUE CALL NOT SENT BY THE ROUTER CALLS NOTHING.** At `draft/v0.35.0`, the loop's step
for a call whose `from` is not the router and whose `value` is `0` leaves the world as it was.
Witnessed by `V35ClaimWitness`. -/
def Properties.V35SkipsZeroValueNonRouterCalls : Prop :=
  ∀ (W : Type) (S : SourceChain W) (router : Address)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (dest baseAsset : Word) (w : W)
    (c : InteropCall),
    c.fromAddr ≠ router → c.value = 0 → v35Step S router baseRecover dest baseAsset w c = some w

/-- **CONFORMING CODE AT THE ROUTER IS ENOUGH AT `draft/v0.35.0`.** If the router's code runs and
answers every call with a well-formed `bool`, the base-token refund never reverts, and the
destination is not L1, the claim of a `Revertable` leg succeeds, whatever the bundle's calls and
whatever runs at any other address. No call needs to recover. Witnessed by `V35ClaimWitness`. -/
def Properties.V35ClaimSucceedsWithConformingRouter : Prop :=
  ∀ (W : Type) (S : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (w : W) (b : Bundle),
    b.destinationChainId ≠ l1ChainId → Conforms S router →
    (∀ w dest asset receiver amount, (baseRecover w dest asset receiver amount).isSome = true) →
      ∃ w', claimRefundV35 S router l1ChainId baseRecover .Revertable w b = some (.Reverted, w')

/-- **THE `draft/v0.35.0` CLAIM REJECTS AN L1 DESTINATION** (`RecoverToL1NotSupported`,
`AtomicFlowManager.sol:299` at `b17415d`), from every leg state and in every world. Witnessed by
`V35ClaimWitness`. -/
def Properties.V35ClaimRejectsL1Destination : Prop :=
  ∀ (W : Type) (S : SourceChain W) (router : Address) (l1ChainId : Word)
    (baseRecover : W → Word → Word → Address → ℕ → Option W) (s : LegState) (w : W) (b : Bundle),
    b.destinationChainId = l1ChainId → claimRefundV35 S router l1ChainId baseRecover s w b = none

/-- **THE `draft/v0.35.0` PREMISES ARE MET, WITH A VALUE-CARRYING DIRECT CALL.** The world is a
counter of refunded base token. The router `9` conforms on `wSourceOver ℕ`, and the base-token
refund adds its amount to the counter and never reverts. The bundle `wValueBundle` goes to chain
`325`, not to L1. Its claim succeeds and refunds the direct call's value `3`. The zero-value direct
call `wDirectCall` is skipped. The same bundle sent to L1 is rejected. -/
def Properties.V35ClaimWitness : Prop :=
  wValueBundle.destinationChainId ≠ wL1
  ∧ Conforms (wSourceOver ℕ) 9
  ∧ (∀ w dest asset receiver amount, (wBaseRecover w dest asset receiver amount).isSome = true)
  ∧ claimRefundV35 (wSourceOver ℕ) 9 wL1 wBaseRecover .Revertable 0 wValueBundle
      = some (.Reverted, 3)
  ∧ wDirectCall.fromAddr ≠ 9 ∧ wDirectCall.value = 0
  ∧ v35Step (wSourceOver ℕ) 9 wBaseRecover 325 1 4 wDirectCall = some 4
  ∧ claimRefundV35 (wSourceOver ℕ) 9 wL1 wBaseRecover .Revertable 0
      { wValueBundle with destinationChainId := wL1 } = none

/-- **ON THE TWO-CALL BUNDLE, ONLY THE PINNED CLAIM DEPENDS ON THE CODE AT THE DIRECT CALL'S
TARGET.** `wSource` and `wSourceConforming` agree at the router `9` and differ at `5`. The pinned
claims of the two-call bundle differ. The `draft/v0.35.0` claims agree, for every base-token
refund. -/
def Properties.DirectTargetCodeDecidesOnlyThePinnedClaim : Prop :=
  (∀ w, wSource.runsCode w 9 = wSourceConforming.runsCode w 9)
  ∧ (∀ w dest data, wSource.exec w 9 dest data = wSourceConforming.exec w 9 dest data)
  ∧ wSource.runsCode () 5 ≠ wSourceConforming.runsCode () 5
  ∧ claimRefundPinned wSource .Revertable () mixD.bundle
      ≠ claimRefundPinned wSourceConforming .Revertable () mixD.bundle
  ∧ ∀ baseRecover : Unit → Word → Word → Address → ℕ → Option Unit,
      claimRefundV35 wSource 9 wL1 baseRecover .Revertable () mixD.bundle
        = claimRefundV35 wSourceConforming 9 wL1 baseRecover .Revertable () mixD.bundle

/-- **THE `draft/v0.35.0` CLAIM OF THE TWO-CALL BUNDLE SUCCEEDS ON `wSource`**, whatever the
base-token refund would do. The bundle carries no value, so that refund is never called. On the
same source chain every pinned claim of that bundle reverts
(`DirectCallWithoutSourceCodeBlocksClaimWitness`). -/
def Properties.V35ClaimSucceedsOnMixedBundle : Prop :=
  ∀ baseRecover : Unit → Word → Word → Address → ℕ → Option Unit,
    claimRefundV35 wSource 9 wL1 baseRecover .Revertable () mixD.bundle = some (.Reverted, ())

end Contracts.AtomicFlowManager.RecoveryLimitsFaithful
