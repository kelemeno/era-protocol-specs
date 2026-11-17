import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryTargets

/-!
# Properties: what `_recoverBundle` finds at each call's `to`

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryTargets`. Proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryTargets`. A bare `:N` is a line of
`atomic-interop/AtomicFlowManager.sol` at the pin.

`_recoverBundle` asks the code deployed **on the source chain** at each call's `to`, a
destination-side address. Three consequences, each a theorem below:

* **Characterization.** Under `VmCall`, a claim succeeds exactly when every call's target holds a
  recoverer, the recoverers all return on the threaded world, and at least one returns `true`
  (`ClaimSucceedsIff`). The manager reads only `to` and `data`; the call's `from`, the indirect
  sender that took the funds on the source chain, is never consulted
  (`RecoveryReadsOnlyTargetAndData`).
* **A target with no recoverer blocks the whole claim**, in every world and for every leg state, so
  no retry helps (`NonRecovererTargetBlocksClaim`). The typical atomic bundle — a router deposit and
  then a call to the destination application — is never refunded when the application does not
  exist on the source chain, although its router call alone would be
  (`DestinationOnlyTargetBlocksRefund`, on the router model of
  `AssetRouterBase/Specs/AtomicRecovery.lean`).
* **Any code that answers `true` counts as recovered** (`ForeignTrueCountsAsRecovered`). Concretely
  (`ForeignTrueStrandsEscrow`): an unrelated contract at the destination-side address answers
  `true`, the claim succeeds and the leg is `Reverted` for good, and the escrow the indirect sender
  holds is untouched, although that sender's own recoverer would have released it.

The router model of B1 is the special case in which every target holds a recoverer
(`RouterModelIsACodeMap`), and for an L2-to-L2 router leg the source chain's router is reached and
refunds the depositor (`SourceRouterTargetRefundsDepositor`, which composes B1's
`PreparedBurnRefundsDepositor`).

Every property with premises has a satisfiability witness: `VmCallHolds` (for `VmCall`, the only
premise of `RouterModelIsACodeMap`), `ClaimSucceedsIffWitness`,
`RecoveryReadsOnlyTargetAndDataWitness`, `NonRecovererTargetBlocksClaimWitness`,
`ForeignTrueStrandsEscrow` (which meets the premises of `ForeignTrueCountsAsRecovered`) and
`SourceRouterTargetRefundsDepositorWitness`.
-/

namespace Contracts.AtomicFlowManager.RecoveryTargets

open Contracts.AtomicFlowManager (LegState)

/-! ## The premise is satisfiable -/

/-- **`VmCall` HOLDS FOR THE SEMANTICS IT DESCRIBES**, at every world and data type. -/
def Properties.VmCallHolds : Prop :=
  ∀ (W D : Type), VmCall (vmCall : CallSem W D)

/-! ## Characterization -/

/-- **(h) A CLAIM SUCCEEDS IFF EVERY TARGET IS A RECOVERER THAT RETURNS, AND ONE RETURNS `true`.**
Under `VmCall`, `claimRefund` on a `Revertable` leg ends in `Reverted` with world `w'` exactly when
every call's target holds recoverer code, the recoverers return in turn on the threaded world
(ending in `w'`), and at least one of them returned `true` (:225-229). What they returned `true`
for — whether anything was refunded — is not consulted. -/
def Properties.ClaimSucceedsIff : Prop :=
  ∀ (W D A C : Type) (sem : CallSem W D) (code : A → Code W D) (target : C → A) (data : C → D)
    (dest : UInt256) (w w' : W) (calls : List C), VmCall sem →
    (claimRefund (recoverStep sem code target data dest) LegState.Revertable w calls
        = some (LegState.Reverted, w') ↔
      ∃ bs, RecoverersReturn code target data dest w calls bs w' ∧ true ∈ bs)

/-- **THE MANAGER READS ONLY `to` AND `data`.** Two calls with the same target and data are
recovered identically, whatever their `from` and `value` (:224-225). In particular the indirect
sender (`InteropCall.from`, `InteropCenter.sol:739`), the source-chain contract that took the
funds, is never asked. -/
def Properties.RecoveryReadsOnlyTargetAndData : Prop :=
  ∀ (W D A C : Type) (sem : CallSem W D) (code : A → Code W D) (target : C → A) (data : C → D)
    (dest : UInt256) (w : W) (c c' : C), target c = target c' → data c = data c' →
    recoverStep sem code target data dest w c = recoverStep sem code target data dest w c'

/-! ## A target with no recoverer -/

/-- **(g) A TARGET WITH NO RECOVERER BLOCKS THE WHOLE CLAIM, PERMANENTLY.** Under `VmCall`, if some
call's target has nothing deployed, or code without `recoverAtomicCall`, on the chain running the
refund, then `claimRefund` reverts for every leg state and in every world. The other calls'
recoveries are rolled back with it, and since the code map is not part of the world, no change of
the world makes a retry succeed. -/
def Properties.NonRecovererTargetBlocksClaim : Prop :=
  ∀ (W D A C : Type) (sem : CallSem W D) (code : A → Code W D) (target : C → A) (data : C → D)
    (dest : UInt256) (calls : List C), VmCall sem →
    (∃ c ∈ calls, NoRecovererAt code (target c)) →
    ∀ (s : LegState) (w : W), claimRefund (recoverStep sem code target data dest) s w calls = none

section RouterInstance

open Contracts.AssetRouter (AssetIdOf AssetId Address Chain)
open Contracts.AssetRouter.AtomicRecovery (Config Hooks World Call CallData MintData routerCall
  directCall AtomicBundleValid)

/-- **(g), CONCRETE: A ROUTER DEPOSIT FOLLOWED BY A CALL TO A DESTINATION-ONLY APPLICATION IS NEVER
REFUNDED.** On the router model of `AssetRouterBase/Specs/AtomicRecovery.lean`: an atomic bundle of
a router-produced deposit and a direct call to an application `app` that is deployed on the
destination only (nothing at its address on the source chain). The bundle passes
`_validateAtomicBundle` (`InteropCenter.sol:670-677`). The deposit alone would be refunded, yet the
bundle's claim reverts for every leg state and in every world. -/
def Properties.DestinationOnlyTargetBlocksRefund : Prop :=
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

/-- **THE ROUTER MODEL IS A CODE MAP.** B1's refund step (`recoverCall`: the router's
`recoverAtomicCall` at the router's address, an arbitrary `other target` elsewhere) is this file's
`recoverStep` under any `VmCall` semantics with `routerCodeMap`, and B1's loop is this file's
loop. So B1's results describe the special case in which every target holds a recoverer; a target
with nothing deployed, or without the function, is `NonRecovererTargetBlocksClaim`'s case. -/
def Properties.RouterModelIsACodeMap : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool)) (dest : Chain)
    (sem : CallSem (World X) CallData), VmCall sem →
    (∀ (w : World X) (c : Call),
      Contracts.AssetRouter.AtomicRecovery.recoverCall enc cfg hk other dest w c
        = recoverStep sem (routerCodeMap enc cfg hk other) Call.target Call.data dest w c) ∧
    ∀ (step : World X → Call → Option (World X × Bool)) (w : World X) (calls : List Call),
      Contracts.AssetRouter.AtomicRecovery.recoverBundle step w calls = recoverBundle step w calls

/-- **(f), REFUND SIDE: A ROUTER LEG WHOSE `to` IS THE SOURCE CHAIN'S ROUTER REFUNDS THE
DEPOSITOR.** For an L2-to-L2 leg the router's bundle call targets `L2_ASSET_ROUTER_ADDR`
(`L2AssetRouter.sol:336`, `AssetRouterBase.sol:365, 374-376`), the same address on every chain. If
the source chain's code there is the router's `recoverAtomicCall`, the manager reaches it, and —
by B1's `PreparedBurnRefundsDepositor` — the call carrying a prepared burn's returned mint data is
refunded by minting exactly the burned amount to the depositor, on a vault that knows the asset,
unpaused, once the tracker hook returns. -/
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
is not the remote receiver and a refund that returns `true`. -/
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

/-! ## Any `true` counts -/

/-- **(h) ANY CODE THAT ANSWERS `true` COUNTS AS RECOVERED.** Under `VmCall`, if every call of a
nonempty bundle targets code that answers `true` and changes nothing, the claim succeeds, the leg
is `Reverted` (terminal: `claimRefund` needs `Revertable`, :170), and the world is exactly as
before. A successful claim therefore does not mean anything was refunded. -/
def Properties.ForeignTrueCountsAsRecovered : Prop :=
  ∀ (W D A C : Type) (sem : CallSem W D) (code : A → Code W D) (target : C → A) (data : C → D)
    (dest : UInt256) (w : W) (calls : List C), VmCall sem → calls ≠ [] →
    (∀ c ∈ calls, ∃ f, code (target c) = .recoverer f ∧ ∀ u, f u dest (data c) = some (u, true)) →
    claimRefund (recoverStep sem code target data dest) LegState.Revertable w calls
      = some (LegState.Reverted, w)

/-- **(h), CONCRETE: A FOREIGN `true` STRANDS THE ESCROW.** The world is the amount `5` the indirect
sender `1` escrowed for the depositor. The bundle has one call, `to = 2` (a destination-side
address; on the source chain an unrelated contract there answers `true`) and `from = 1`. The
premises of `ForeignTrueCountsAsRecovered` hold; the claim succeeds with the escrow still `5`;
the leg is then `Reverted`, so no claim can follow; and the indirect sender's own recoverer, had the
manager asked `from`, would have released the escrow. -/
def Properties.ForeignTrueStrandsEscrow : Prop :=
  ∃ (sem : CallSem ℕ Unit) (c : TriCall),
    VmCall sem ∧ c.1 ≠ c.2.1 ∧
    (∃ f, escrowCode (TriCall.target c) = .recoverer f ∧ ∀ u, f u 0 (TriCall.data c) = some (u, true)) ∧
    claimRefund (recoverStep sem escrowCode TriCall.target TriCall.data 0) LegState.Revertable 5 [c]
      = some (LegState.Reverted, 5) ∧
    (∀ w, claimRefund (recoverStep sem escrowCode TriCall.target TriCall.data 0) LegState.Reverted
      w [c] = none) ∧
    recoverStep sem escrowCode (fun c : TriCall => c.2.1) TriCall.data 0 5 c = some (0, true)

/-! ## Witnesses -/

/-- **`ClaimSucceedsIff` IS NOT ONE-SIDED.** Under `VmCall`, a two-call bundle whose recoverers
return `true` then `false`: the recoverers' run exists with a `true` and a `false` (so the right
side holds and the bundle is only partly recovered), and the claim succeeds; and a bundle whose
only recoverer returns `false` is not claimable. -/
def Properties.ClaimSucceedsIffWitness : Prop :=
  ∃ (sem : CallSem ℕ Unit) (calls : List TriCall) (c : TriCall) (w' : ℕ),
    VmCall sem ∧ calls.length = 2 ∧
    (∃ bs, RecoverersReturn escrowCode TriCall.target TriCall.data 0 5 calls bs w' ∧ true ∈ bs ∧
      false ∈ bs) ∧
    claimRefund (recoverStep sem escrowCode TriCall.target TriCall.data 0) LegState.Revertable 5 calls
      = some (LegState.Reverted, w') ∧
    claimRefund (recoverStep sem escrowCode TriCall.target TriCall.data 0) LegState.Revertable 5 [c]
      = none

/-- **`RecoveryReadsOnlyTargetAndData` APPLIES TO DIFFERENT CALLS.** Two different calls with the
same `to` and `data` and different `from` (the second sender is the escrow holder `1`). -/
def Properties.RecoveryReadsOnlyTargetAndDataWitness : Prop :=
  ∃ c c' : TriCall, c ≠ c' ∧ TriCall.target c = TriCall.target c' ∧ TriCall.data c = TriCall.data c'

/-- **`NonRecovererTargetBlocksClaim`'S PREMISES ARE SATISFIABLE**, on a two-call bundle whose other
call would be refunded on its own. -/
def Properties.NonRecovererTargetBlocksClaimWitness : Prop :=
  ∃ (sem : CallSem ℕ Unit) (calls : List TriCall),
    VmCall sem ∧ calls.length = 2 ∧ (∃ c ∈ calls, NoRecovererAt escrowCode (TriCall.target c)) ∧
    ∃ c ∈ calls, (claimRefund (recoverStep sem escrowCode TriCall.target TriCall.data 0)
      LegState.Revertable 5 [c]).isSome = true

end Contracts.AtomicFlowManager.RecoveryTargets
