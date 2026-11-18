import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryTargets

/-!
# Properties: what `_recoverBundle` finds at each call's `to`

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryTargets`. Proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryTargets`. A bare `:N` is a line of
`atomic-interop/AtomicFlowManager.sol` at the pin.

`_recoverBundle` calls `recoverAtomicCall` at each call's `to`, on the chain running the refund
(the leg's source chain), and the code deployed there is a parameter of the model (`Code`). Under
the call semantics `VmCall`:

* **Characterization.** A claim of a `Revertable` leg succeeds exactly when every call's target
  holds a recoverer, the recoverers all return on the threaded world, and at least one returns
  `true` (`ClaimSucceedsIff`). Two calls with the same `to` and `data` are recovered identically,
  whatever their `from` and `value` (`RecoveryReadsOnlyTargetAndData`, which holds by the
  definition of `recoverStep`).
* **A target with no recoverer.** If some call's target has nothing deployed, or code without
  `recoverAtomicCall`, the claim reverts in every world and for every leg state
  (`NonRecovererTargetBlocksClaim`). On the router model of `AssetRouterBase/Specs/AtomicRecovery.lean`:
  a bundle of a router-produced call and a direct call to an address with nothing deployed on the
  refunding chain passes `_validateAtomicBundle`; the router call alone is claimable, and the
  two-call bundle's claim reverts in every world and leg state
  (`CodelessCallTargetBlocksBundleClaim`).
* **A returned `true` is counted, whatever the code did.** If every call of a nonempty bundle
  targets code that returns `true` and changes nothing, the claim succeeds, the leg is `Reverted`
  and the world is unchanged (`ForeignTrueCountsAsRecovered`).

The router model is the special case in which every target holds a recoverer
(`RouterModelIsACodeMap`). A router call to another L2 targets `L2_ASSET_ROUTER_ADDR`, the router's
own address on the source chain; where the router's `recoverAtomicCall` is deployed there, the
manager's call of a prepared burn's call re-mints the burned amount to the depositor
(`SourceRouterTargetRefundsDepositor`, which composes `AtomicRecovery`'s
`PreparedBurnRefundsDepositor`).

Every property with premises has a witness meeting all of them: `VmCallHolds` (for `VmCall`, the
only premise of `RouterModelIsACodeMap`), `ClaimSucceedsIffWitness`,
`RecoveryReadsOnlyTargetAndDataWitness`, `NonRecovererTargetBlocksClaimWitness`,
`ForeignTrueCountsAsRecoveredWitness` and `SourceRouterTargetRefundsDepositorWitness`.
`CodelessCallTargetBlocksBundleClaim` is itself an instance. `VmCall` is load-bearing: under
semantics in which a call to an address without code returns `true`, such a target's bundle is
claimable (`NonRecovererTargetBlocksClaimNeedsVmCall`).

Two of these restate known results in the code-map form, and are close to definitional under
`VmCall`, whose modelling premise is their content: `NonRecovererTargetBlocksClaim` is
`AttackVectors.RecoveryLimits.revert_anywhere_blocks` with the revert located at a target with
no recoverer, and `ForeignTrueCountsAsRecovered` generalizes `AssetRouterBase`'s
`Contracts.AssetRouter.AtomicRecoveryFaithful.Properties.L1LegForeignTrueClosesWithoutRefund`
and `L1LegClaimOnlyByForeignCode` from the L1 leg to any nonempty bundle.
-/

namespace Contracts.AtomicFlowManager.RecoveryTargets

open Contracts.AtomicFlowManager (LegState)

/-! ## The premise is satisfiable -/

/-- **`VmCall` HOLDS FOR THE SEMANTICS IT DESCRIBES**, at every world and data type. -/
def Properties.VmCallHolds : Prop :=
  ∀ (W D : Type), VmCall (vmCall : CallSem W D)

/-! ## Characterization -/

/-- **A CLAIM SUCCEEDS IFF EVERY TARGET IS A RECOVERER THAT RETURNS, AND ONE RETURNS `true`.**
Under `VmCall`, `claimRefund` on a `Revertable` leg ends in `Reverted` with world `w'` exactly when
every call's target holds recoverer code, the recoverers return in turn on the threaded world
(ending in `w'`), and at least one of them returned `true` (:225-229). The condition reads only the
returned booleans, not what the recoverers did to the world. -/
def Properties.ClaimSucceedsIff : Prop :=
  ∀ (W D A C : Type) (sem : CallSem W D) (code : A → Code W D) (target : C → A) (data : C → D)
    (dest : UInt256) (w w' : W) (calls : List C), VmCall sem →
    (claimRefund (recoverStep sem code target data dest) LegState.Revertable w calls
        = some (LegState.Reverted, w') ↔
      ∃ bs, RecoverersReturn code target data dest w calls bs w' ∧ true ∈ bs)

/-- **THE MANAGER READS ONLY `to` AND `data`.** Two calls with the same target and data are
recovered identically, whatever their other fields (:224-225). In particular `InteropCall.from`
(for an indirect call, the indirect sender, `InteropCenter.sol:739`) and `value` are not read. This
holds by the definition of `recoverStep`; it records that the model, like the code, passes nothing
else. -/
def Properties.RecoveryReadsOnlyTargetAndData : Prop :=
  ∀ (W D A C : Type) (sem : CallSem W D) (code : A → Code W D) (target : C → A) (data : C → D)
    (dest : UInt256) (w : W) (c c' : C), target c = target c' → data c = data c' →
    recoverStep sem code target data dest w c = recoverStep sem code target data dest w c'

/-! ## A target with no recoverer -/

/-- **A TARGET WITH NO RECOVERER MAKES EVERY CLAIM REVERT, IN EVERY WORLD.** Under `VmCall`, if
some call's target has nothing deployed, or code without `recoverAtomicCall`, on the chain running
the refund, then `claimRefund` reverts for every leg state and in every world, so the other calls'
recoveries do not persist either. The code map is a parameter, not part of the world: a later
deployment at that address is outside the model. -/
def Properties.NonRecovererTargetBlocksClaim : Prop :=
  ∀ (W D A C : Type) (sem : CallSem W D) (code : A → Code W D) (target : C → A) (data : C → D)
    (dest : UInt256) (calls : List C), VmCall sem →
    (∃ c ∈ calls, NoRecovererAt code (target c)) →
    ∀ (s : LegState) (w : W), claimRefund (recoverStep sem code target data dest) s w calls = none

section RouterInstance

open Contracts.AssetRouter (AssetIdOf AssetId Address Chain)
open Contracts.AssetRouter.AtomicRecovery (Config Hooks World Call CallData MintData routerCall
  directCall AtomicBundleValid)

/-- **INSTANCE: A ROUTER CALL AND A DIRECT CALL TO A CODELESS ADDRESS.** On the router model of
`AssetRouterBase/Specs/AtomicRecovery.lean`, under `VmCall`: a bundle of a router-produced call
and a direct call to an address `app` that is not the router and at which nothing is deployed on
the chain running the refund (`routerAndAppCodeMap`). The bundle passes `_validateAtomicBundle`
(`InteropCenter.sol:670-677`). A claim of the router call alone succeeds, and every claim of the
two-call bundle reverts, for every leg state and in every world. -/
def Properties.CodelessCallTargetBlocksBundleClaim : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (sem : CallSem (World X) CallData) (dest : Chain) (w : World X) (a : AssetId) (md : MintData)
    (app sender : Address) (data : CallData),
    VmCall sem ∧ app ≠ cfg.router ∧
    AtomicBundleValid [routerCall cfg a md, directCall app sender data] ∧
    (claimRefund (recoverStep sem (routerAndAppCodeMap enc cfg hk app other) Call.target Call.data
        dest) LegState.Revertable w [routerCall cfg a md]).isSome = true ∧
    ∀ (s : LegState) (w' : World X),
      claimRefund (recoverStep sem (routerAndAppCodeMap enc cfg hk app other) Call.target Call.data
        dest) s w' [routerCall cfg a md, directCall app sender data] = none

/-- **THE ROUTER MODEL IS A CODE MAP.** `AtomicRecovery`'s refund step (`recoverCall`: the router's
`recoverAtomicCall` at the router's address, an arbitrary `other target` elsewhere) is this file's
`recoverStep` under any `VmCall` semantics with `routerCodeMap`, and `AtomicRecovery`'s loop is this
file's loop. So `AtomicRecovery`'s results describe the special case in which every target holds a
recoverer; a target with nothing deployed, or without the function, is
`NonRecovererTargetBlocksClaim`'s case. -/
def Properties.RouterModelIsACodeMap : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool)) (dest : Chain)
    (sem : CallSem (World X) CallData), VmCall sem →
    (∀ (w : World X) (c : Call),
      Contracts.AssetRouter.AtomicRecovery.recoverCall enc cfg hk other dest w c
        = recoverStep sem (routerCodeMap enc cfg hk other) Call.target Call.data dest w c) ∧
    ∀ (step : World X → Call → Option (World X × Bool)) (w : World X) (calls : List Call),
      Contracts.AssetRouter.AtomicRecovery.recoverBundle step w calls = recoverBundle step w calls

/-- **A ROUTER CALL WHOSE `to` IS THE SOURCE CHAIN'S ROUTER REFUNDS THE DEPOSITOR.**
`routerCall` targets `L2_ASSET_ROUTER_ADDR`, the router's own address on the source chain; it is
the call the router produces for a destination other than L1 (`L2AssetRouter.sol:336`,
`AssetRouterBase.sol:365, 374-376`; `AtomicRecoveryFaithful.Properties.RouterCallToL2IsModelled`).
Under `VmCall`, if the source chain's code at that address is the router's `recoverAtomicCall`, the
manager's call of the router call carrying a prepared burn's returned mint data is the vault's mint
of exactly the burned amount `r.data.amount` to the depositor `r.depositor` (the `mint` hook:
`true` with the hook's world when it returns, a revert when it reverts), as `AtomicRecovery`'s
`PreparedBurnRefundsDepositor` states. Premises: the world is unpaused, its vault has a token for
the asset and an origin chain other than this one, and the tracker hook returns. The world's vault
is not tied to the vault that burned. -/
def Properties.SourceRouterTargetRefundsDepositor : Prop :=
  ∀ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc),
    NativeTokenVaultBase.WellFormed s → NativeTokenVaultBase.prepare prepHooks s r = some out →
    ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
      (sem : CallSem (World X) CallData) (code : Address → Code (World X) CallData) (dest : Chain)
      (w : World X) (x₁ : X),
      VmCall sem → code cfg.router = .recoverer (routerRecoverer enc cfg hk) →
      w.paused = false → w.vault.originChain r.assetId ≠ cfg.thisChain →
      w.vault.token r.assetId ≠ 0 → hk.fromChain w.rest dest r.assetId r.data.amount = some x₁ →
        recoverStep sem code Call.target Call.data dest w (routerCall cfg r.assetId out.data)
          = (hk.mint x₁ (w.vault.token r.assetId) r.depositor r.data.amount).map
              (fun x₂ => ({ w with rest := x₂ }, true))

/-- **`SourceRouterTargetRefundsDepositor`'S PREMISES ARE JOINTLY SATISFIABLE**, with a depositor who
is not the remote receiver and a call that returns `true`. The instance is `AtomicRecovery`'s
`PreparedBurnRefundSatisfiable` with `routerCodeMap`. -/
def Properties.SourceRouterTargetRefundsDepositorWitness : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (sem : CallSem (World X) CallData) (code : Address → Code (World X) CallData) (dest : Chain)
    (w : World X) (x₁ : X),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    ∧ r.depositor ≠ r.data.receiver
    ∧ VmCall sem ∧ code cfg.router = .recoverer (routerRecoverer enc cfg hk)
    ∧ w.paused = false ∧ w.vault.originChain r.assetId ≠ cfg.thisChain
    ∧ w.vault.token r.assetId ≠ 0 ∧ hk.fromChain w.rest dest r.assetId r.data.amount = some x₁
    ∧ ∃ w', recoverStep sem code Call.target Call.data dest w (routerCall cfg r.assetId out.data)
        = some (w', true)

end RouterInstance

/-! ## A returned `true` is counted -/

/-- **A RETURNED `true` IS COUNTED, WHATEVER THE CODE DID.** Under `VmCall`, if every call of a
nonempty bundle targets code that returns `true` and leaves the world as it was, the claim of a
`Revertable` leg succeeds: the leg is `Reverted` and the world is exactly as before. So a
successful claim does not imply that the world changed. -/
def Properties.ForeignTrueCountsAsRecovered : Prop :=
  ∀ (W D A C : Type) (sem : CallSem W D) (code : A → Code W D) (target : C → A) (data : C → D)
    (dest : UInt256) (w : W) (calls : List C), VmCall sem → calls ≠ [] →
    (∀ c ∈ calls, ∃ f, code (target c) = .recoverer f ∧ ∀ u, f u dest (data c) = some (u, true)) →
    claimRefund (recoverStep sem code target data dest) LegState.Revertable w calls
      = some (LegState.Reverted, w)

/-- **`ForeignTrueCountsAsRecovered`'S PREMISES HOLD, ON A CALL WHOSE `from` HOLDS OTHER CODE.**
On `witnessCode`, under `VmCall`: a one-call bundle whose target's code returns `true` and changes
nothing, and whose `from` differs from its `to` (in the proof, `to = 2` and `from = 1`). From world
`5` the claim succeeds with the world still `5`, and a claim of the now `Reverted` leg reverts in
every world. The code at the call's `from` returns `true` from world `5` and sets it to `0`, so
which of the two addresses is asked changes the outcome. -/
def Properties.ForeignTrueCountsAsRecoveredWitness : Prop :=
  ∃ (sem : CallSem ℕ Unit) (c : TriCall),
    VmCall sem ∧ c.1 ≠ c.2.1 ∧
    (∃ f, witnessCode (TriCall.target c) = .recoverer f ∧ ∀ u, f u 0 (TriCall.data c) = some (u, true)) ∧
    claimRefund (recoverStep sem witnessCode TriCall.target TriCall.data 0) LegState.Revertable 5 [c]
      = some (LegState.Reverted, 5) ∧
    (∀ w, claimRefund (recoverStep sem witnessCode TriCall.target TriCall.data 0) LegState.Reverted
      w [c] = none) ∧
    recoverStep sem witnessCode (fun c : TriCall => c.2.1) TriCall.data 0 5 c = some (0, true)

/-! ## Witnesses -/

/-- **`ClaimSucceedsIff`'S PREMISE HOLDS, AND BOTH SIDES ARE EXERCISED.** Under `VmCall`, on
`witnessCode`: a two-call bundle whose recoverers return in turn with a `true` and a `false` among
the returned booleans, so the right side holds, and the claim succeeds; and a one-call bundle that
is not claimable. -/
def Properties.ClaimSucceedsIffWitness : Prop :=
  ∃ (sem : CallSem ℕ Unit) (calls : List TriCall) (c : TriCall) (w' : ℕ),
    VmCall sem ∧ calls.length = 2 ∧
    (∃ bs, RecoverersReturn witnessCode TriCall.target TriCall.data 0 5 calls bs w' ∧ true ∈ bs ∧
      false ∈ bs) ∧
    claimRefund (recoverStep sem witnessCode TriCall.target TriCall.data 0) LegState.Revertable 5 calls
      = some (LegState.Reverted, w') ∧
    claimRefund (recoverStep sem witnessCode TriCall.target TriCall.data 0) LegState.Revertable 5 [c]
      = none

/-- **`RecoveryReadsOnlyTargetAndData`'S PREMISES HOLD FOR DIFFERENT CALLS.** Two different calls with
the same `to` and `data` and different `from`. -/
def Properties.RecoveryReadsOnlyTargetAndDataWitness : Prop :=
  ∃ c c' : TriCall, c ≠ c' ∧ TriCall.target c = TriCall.target c' ∧ TriCall.data c = TriCall.data c'

/-- **`NonRecovererTargetBlocksClaim` NEEDS `VmCall`.** Under call semantics in which a call to an
address without code returns `true` and changes nothing (and is otherwise `vmCall`), a one-call
bundle whose target has nothing deployed on `witnessCode` is claimable. -/
def Properties.NonRecovererTargetBlocksClaimNeedsVmCall : Prop :=
  ∃ (sem : CallSem ℕ Unit) (c : TriCall),
    (∀ w dest d, sem .none w dest d = some (w, true)) ∧
    (∀ f w dest d, sem (.recoverer f) w dest d = f w dest d) ∧
    witnessCode (TriCall.target c) = .none ∧
    claimRefund (recoverStep sem witnessCode TriCall.target TriCall.data 0) LegState.Revertable 5 [c]
      = some (LegState.Reverted, 5)

/-- **`NonRecovererTargetBlocksClaim`'S PREMISES ARE SATISFIABLE**, on a two-call bundle whose other
call would be claimable on its own. -/
def Properties.NonRecovererTargetBlocksClaimWitness : Prop :=
  ∃ (sem : CallSem ℕ Unit) (calls : List TriCall),
    VmCall sem ∧ calls.length = 2 ∧ (∃ c ∈ calls, NoRecovererAt witnessCode (TriCall.target c)) ∧
    ∃ c ∈ calls, (claimRefund (recoverStep sem witnessCode TriCall.target TriCall.data 0)
      LegState.Revertable 5 [c]).isSome = true

end Contracts.AtomicFlowManager.RecoveryTargets
