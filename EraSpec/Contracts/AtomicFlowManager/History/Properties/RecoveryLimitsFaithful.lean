import EraSpec.Core.Headline
import EraSpec.Contracts.AtomicFlowManager.History.Specs.RecoveryLimitsFaithful

/-!
# Properties (History): the pinned refund loop over each call's `to`

Statements about `EraSpec.Contracts.AtomicFlowManager.History.Specs.RecoveryLimitsFaithful`, proved
in `EraSpec.Contracts.AtomicFlowManager.History.Proofs.RecoveryLimitsFaithful`.

**History.** This is the record of the refund loop at era-contracts `c67894b9`
(`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), not a claim about `draft/v0.35.0` `b17415d20`. At the
pin, `_recoverBundle` (`atomic-interop/AtomicFlowManager.sol:219-230`) called
`IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)` on every call, counted the calls
that answered `true`, and reverted when none did (`:229`); `claimRefund` (`:165-180`) gated on
`Revertable` (`:169-170`) and wrote `Reverted` first (`:175`). At `b17415d20` the loop calls only
the asset router and counts nothing: that loop is `claimRefundV35` in
`Specs/RecoveryLimitsFaithful.lean`. Line numbers here are at the pin. `c.to` is what the pin's
`_processCallStarter` (`interop/InteropCenter.sol:701-751`) wrote into the bundle: for a direct
call the starter's recipient (`:745`), for an indirect call the address the indirect sender
returned (`:736`). The bundles are `Contracts.InteropCenter`'s, at the pin (`MODEL-CENTER`).

* The pinned call of `c.to` reverts exactly when `c.to` runs no code or answers nothing that decodes
  as a `bool` (`PinnedCallRevertsIff`, `CodelessTargetReverts`).
* A claim of a `Revertable` leg succeeds exactly when the loop's outcomes satisfy
  `AttackVectors.RecoveryLimits.ClaimAccepted` (`PinnedClaimSucceedsIffAccepted`); it is a `claim`
  step of the manager model (`PinnedClaimIsAManagerClaimStep`); Limit 2 holds on the threaded world
  (`PinnedRevertAnywhereBlocks`).
* A target that runs no code, or never answers a `bool`, makes the claim revert
  (`CodelessTargetBlocksClaim`, `CodelessTargetBlocksEveryClaim`,
  `NonAnsweringTargetBlocksEveryClaim`, `DirectCallWithoutSourceCodeBlocksClaim`); success needs code
  answering at every target (`ClaimSuccessNeedsCodeAtEveryTarget`); conforming targets, one of which
  recovers, suffice (`ConformingTargetsRefund`).
* On the two-call bundle only the pinned claim depends on the code at the direct call's target
  (`DirectTargetCodeDecidesOnlyThePinnedClaim`).

The witnesses use a two-call leg that the pin's center and manager bring to `Revertable`.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsFaithful.History

open AttackVectors.RecoveryLimits (Outcome ClaimAccepted)
open Contracts.InteropCenter (Address Word InteropCall Bundle CallStarter FormsCall)
open Contracts.InteropCenter.History (Dispatch FormedBy)

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
  ∀ (P : Contracts.InteropCenter.History.Params) (d : Dispatch) (cs : CallStarter) (W : Type)
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
  Contracts.InteropCenter.History.Reach Contracts.InteropCenter.History.deployed Contracts.InteropCenter.History.wParams
      Contracts.InteropCenter.History.init mixS2
  ∧ mixS2.manager.legState mixD.atomicSend.flowId
      (Contracts.InteropCenter.History.bundleHash Contracts.InteropCenter.History.wParams mixD.bundle) = .Revertable
  ∧ FormedBy Contracts.InteropCenter.History.wParams mixD
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
        (Contracts.InteropCenter.History.bundleHash Contracts.InteropCenter.History.wParams mixD.bundle))
      () mixD.bundle = some (.Reverted, ())
  ∧ Contracts.InteropCenter.History.Reach Contracts.InteropCenter.History.deployed Contracts.InteropCenter.History.wParams
      Contracts.InteropCenter.History.init
      { mixS2 with
        manager := mixS2.manager.set 7
          (Contracts.InteropCenter.History.bundleHash Contracts.InteropCenter.History.wParams mixD.bundle)
          .Reverted }

/-- **ON THE TWO-CALL BUNDLE, ONLY THE PINNED CLAIM DEPENDS ON THE CODE AT THE DIRECT CALL'S
TARGET.** `wSource` and `wSourceConforming` agree at the router `9` and differ at `5`. The pinned
claims of the two-call bundle differ. The `draft/v0.35.0` claims agree, for every base-token
refund. -/
@[witness] def Properties.DirectTargetCodeDecidesOnlyThePinnedClaim : Prop :=
  (∀ w, wSource.runsCode w 9 = wSourceConforming.runsCode w 9)
  ∧ (∀ w dest data, wSource.exec w 9 dest data = wSourceConforming.exec w 9 dest data)
  ∧ wSource.runsCode () 5 ≠ wSourceConforming.runsCode () 5
  ∧ claimRefundPinned wSource .Revertable () mixD.bundle
      ≠ claimRefundPinned wSourceConforming .Revertable () mixD.bundle
  ∧ ∀ baseRecover : Unit → Word → Word → Address → ℕ → Option Unit,
      claimRefundV35 wSource 9 wL1 baseRecover .Revertable () mixD.bundle
        = claimRefundV35 wSourceConforming 9 wL1 baseRecover .Revertable () mixD.bundle

end Contracts.AtomicFlowManager.RecoveryLimitsFaithful.History
