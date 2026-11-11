import EraSpec.Protocol.InteropAtomicity.Specs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg

/-!
# Model: pause flags on the atomic-interop path

`Contracts.FlowBinding.RunLog` (`Specs/FlowBinding.lean`) is every interleaving of every
chain's manager calls and every destination's gate calls.  It omits the pause checks, and
its header says why that is safe: they can only reject a call.  This file puts them back.
Each chain gets one pause flag per pausable contract on the path, two steps that set and
clear a flag, and a gate on each step that the source routes through a paused contract.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.Pause`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.Pause`.

Sources: the pinned era-contracts tree `c67894b9`, under `l1-contracts/contracts/`.

## Which contracts on the path can be paused

All three are OpenZeppelin v4 `PausableUpgradeable`, with `pause()` and `unpause()`
restricted to the owner.  `_pause` carries `whenNotPaused`, `_unpause` carries `whenPaused`,
and a fresh proxy starts unpaused.

* **The `InteropCenter`** (`interop/InteropCenter.sol:84`; `pause`/`unpause` at `:928-935`).
  Both callers of `_sendBundle` are `whenNotPaused`: `sendMessage` (`:213-217`, call at
  `:247`) and `sendBundle` (`:262-266`, call at `:320`).  `_sendBundle` reaches
  `_dispatchBundle` (`:574`), the only place that calls `AtomicFlowManager.append`
  (`:650-655`).  So a paused center blocks every `append` on its chain.
* **The `L2AssetRouter`** (`bridge/asset-router/AssetRouterBase.sol:37`; `:390-398`).  On the
  send side, an indirect call through the router runs `initiateIndirectCall`
  (`bridge/asset-router/L2AssetRouter.sol:299-342`), which calls `_bridgehubDeposit`
  (`AssetRouterBase.sol:120-126`, `whenNotPaused`).  The receive side carries no pause gate:
  `receiveMessage` (`AssetRouterBase.sol:215-256`) and `finalizeDeposit`
  (`L2AssetRouter.sol:265-274`).  Neither does the refund side, `recoverAtomicCall`
  (`L2AssetRouter.sol:281-296`).
* **The `NativeTokenVault`** (`bridge/ntv/NativeTokenVaultBase.sol:52`; `:656-668`).  Three
  entry points carry `whenNotPaused`.  `bridgeBurn` (`:315-339`, modifier at `:327`) is the
  source burn.  `bridgeMint` (`:193-205`, at `:197`) is the destination mint, which the
  router's `_finalizeDeposit` calls for an asset whose handler is the vault
  (`AssetRouterBase.sol:275-292`).  `bridgeRecoverFailedTransfer` (`:213-233`, at `:217`) is the
  source refund, which `recoverAtomicCall` calls for EVERY `finalizeDeposit` call, whatever the
  asset's handler (`L2AssetRouter.sol:294`; `Contracts.AssetRouter.AtomicRecovery`).  The
  source says the L2 vault's pause "is kept only for legacy/shared-code reasons and should not
  be used as an emergency mechanism" (`:656-659`).  It is still live.

## What cannot be paused

* **The L2 interop handler.**  `executeAtomicBundle` begins with `_ensureNotPaused()`
  (`interop/interop-handler/L2InteropHandler.sol:50`).  On L2 that is the base contract's
  empty function (`interop/interop-handler/InteropHandlerBase.sol:75-79`: "on L2 it is a no-op
  (the L2 system contract is not pausable)").  `L2InteropHandler` does not override it, and
  only `L1InteropHandler` does (`L1InteropHandler.sol:60-64`).  Atomic bundles execute only on
  L2: `executeAtomicBundle` exists only in `L2InteropHandler` (`:39-49`).  So no handler flag
  is modelled, and there is no "paused destination handler".  A destination pause blocks an
  atomic execution only through a paused contract that the bundle's calls reach.
  `_executeCalls` (`InteropHandlerBase.sol:259-289`) does not catch a failing call, and the
  router's `receiveMessage` re-raises the self-call's revert (`AssetRouterBase.sol:247-254`).
  So a paused destination vault reverts the whole `executeAtomicBundle`.  The handler-level
  consequence, that the bundle stays `Unreceived` and can be retried, is
  `Contracts.InteropHandler.Properties.FailedAttemptCanBeRetried`.
* **The `AtomicFlowManager`.**  None of `append` (`atomic-interop/AtomicFlowManager.sol:87-102`),
  `requireFlowFinalized` (`:105-131`), `authorizeRefund` (`:134-162`) and `claimRefund`
  (`:165-180`) has a pause gate.  `claimRefund` reaches the vault only through
  `_recoverBundle`'s raw call loop (`:219-230`).
* **The `L2AssetTracker`.**  It inherits `PausableUpgradeable` only for storage layout; "the
  owner/pause features are unused on L2" (`bridge/asset-tracker/L2AssetTracker.sol:32-35`),
  and it has no `whenNotPaused`.

## No clock on execution

`requireFlowFinalized` compares each leg's batch timestamp with the flow deadline
(`AtomicInteropProof.verifyInclusion`, `atomic-interop/libraries/AtomicInteropProof.sol:113-139`).
`atomic-interop/libraries/AtomicInteropProof.sol` never reads `block.timestamp`.  So a leg
committed by an on-time batch passes the gate at any later time, and a pause can delay its
execution but cannot expire it.  The model has no current time, which is faithful to this.

## What is modelled

* `Flags`: `paused()` of each chain's center, router and vault.
* `Profile`: what the gates need to know about a bundle.  These are its destination chain and
  which pausable contracts its send, execution and refund reach.  The bundle hash commits to
  the bundle bytes, so each field is a function of the hash.  Every result quantifies over
  every profile.  The intended readings are in the field comments.  Which handler the
  destination router names for an asset can change during a run (`AllWriters`).  A profile
  fixes it, so it is a model boundary of `mintsViaVault`.
* `PRun`: `RunLog`'s five steps, each with its pause gate, and `pause`/`unpause` steps.  The
  trace records every step, most recent first.  `checkedCalls` recovers `RunLog`'s log, the
  calls that ran `_checkFlowId`.  As in `RunLog`, the tree side is the fixed history `System`,
  and the gate checks are the same predicates.
* `PSysSteps`: the same gates and flag steps on `Contracts.AppendPath.SysSteps`, the system run
  in which each chain's tree is attached to its manager, so that an `append` inserts into it.
* Not modelled: pausable contracts other than these three, such as custom asset handlers and
  arbitrary call targets.  A target that reverts while its own pause is set is a reverting
  call in `Contracts.InteropHandler` (`RevertingCallRevertsTheExecution`).  Ownership of the
  pause functions (`OPS-CONFIG`) is not modelled either: the `pause`/`unpause` steps are
  always available to the owner.
-/

namespace Contracts.InteropPause

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Refund
open Contracts.FlowBinding Contracts.AtomicFlowManager

/-! ## Pause flags -/

/-- The pausable contracts on an L2 that an atomic leg's life passes through. -/
inductive Pausable where
  /-- `InteropCenter` (`interop/InteropCenter.sol:84, 928-935`). -/
  | center
  /-- `L2AssetRouter` (`bridge/asset-router/AssetRouterBase.sol:37, 390-398`). -/
  | router
  /-- `L2NativeTokenVault` (`bridge/ntv/NativeTokenVaultBase.sol:52, 656-668`). -/
  | vault
deriving DecidableEq, Repr

/-- Every chain's pause flags: `P c k` is `paused()` of chain `c`'s contract `k`. -/
abbrev Flags := Chain → Pausable → Bool

/-- Nothing paused anywhere: the flags of fresh deployments. -/
def noFlags : Flags := fun _ _ => false

/-- Set chain `c`'s flag for contract `k` to `v`. -/
def Flags.set (P : Flags) (c : Chain) (k : Pausable) (v : Bool) : Flags :=
  fun c' k' => if c' = c ∧ k' = k then v else P c' k'

/-! ## What the gates read about a bundle -/

/-- What the pause gates need to know about the bundle with a given hash.  The hash commits
to the bundle's bytes (`InteropDataEncoding.encodeInteropBundleHash`), so each field is a
function of the hash. -/
structure Profile where
  /-- `InteropBundle.destinationChainId`: the chain whose handler runs `executeAtomicBundle`. -/
  dest : UInt256 → Chain
  /-- The bundle has an indirect call through the source router, so `sendBundle` runs
  `initiateIndirectCall` → `_bridgehubDeposit` (`whenNotPaused`, `AssetRouterBase.sol:126`). -/
  sendsViaRouter : UInt256 → Bool
  /-- Such a call is for an asset whose source handler is the vault, so `_burn` calls
  `bridgeBurn` (`whenNotPaused`, `NativeTokenVaultBase.sol:327`). -/
  burnsViaVault : UInt256 → Bool
  /-- The bundle has a router `finalizeDeposit` call for an asset whose destination handler is
  the vault, so executing it reaches `bridgeMint` (`whenNotPaused`,
  `NativeTokenVaultBase.sol:197`). -/
  mintsViaVault : UInt256 → Bool
  /-- The bundle has a router `finalizeDeposit` call, so `claimRefund`'s `recoverAtomicCall`
  reaches `bridgeRecoverFailedTransfer` (`whenNotPaused`, `NativeTokenVaultBase.sol:217`),
  whatever the asset's handler. -/
  recoversViaVault : UInt256 → Bool

/-- **THE SEND GATE.**  `sendBundle` of the bundle with hash `b` on chain `c` passes every
pause check it meets.  The center's is unconditional (`InteropCenter.sol:217, 266`).  The
router's and the vault's apply when the bundle reaches them. -/
def SendOpen (prof : Profile) (P : Flags) (c : Chain) (b : UInt256) : Prop :=
  P c .center = false ∧ (prof.sendsViaRouter b = true → P c .router = false)
    ∧ (prof.burnsViaVault b = true → P c .vault = false)

/-- **THE EXECUTION GATE.**  `executeAtomicBundle` of the bundle with hash `b` passes every
pause check it meets.  The handler's own `_ensureNotPaused` is a no-op on L2 and contributes
nothing.  The destination vault's `bridgeMint` applies when the bundle mints through it. -/
def ExecOpen (prof : Profile) (P : Flags) (b : UInt256) : Prop :=
  prof.mintsViaVault b = true → P (prof.dest b) .vault = false

/-- **THE REFUND GATE.**  `claimRefund` of the bundle with hash `b` on its source chain `c`
passes every pause check it meets.  The manager and `recoverAtomicCall` have none.  The
source vault's `bridgeRecoverFailedTransfer` applies when the bundle has a router call. -/
def RecoverOpen (prof : Profile) (P : Flags) (c : Chain) (b : UInt256) : Prop :=
  prof.recoversViaVault b = true → P c .vault = false

instance (prof : Profile) (P : Flags) (c : Chain) (b : UInt256) : Decidable (SendOpen prof P c b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (prof : Profile) (P : Flags) (b : UInt256) : Decidable (ExecOpen prof P b) :=
  inferInstanceAs (Decidable (_ → _))

instance (prof : Profile) (P : Flags) (c : Chain) (b : UInt256) :
    Decidable (RecoverOpen prof P c b) :=
  inferInstanceAs (Decidable (_ → _))

/-- **EXECUTION THROUGH THE GATE, UNDER PAUSE.**  `ExecutedViaBy` (the deployed atomicity gate
on the named evidence `ev`) and the execution gate open at flags `P`. -/
def ExecutedViaPausedBy (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (prof : Profile) (P : Flags) (F : Flow) (ev : GateEvidence)
    (leg : FlowLeg) : Prop :=
  ExecOpen prof P leg.bundleHash ∧ ExecutedViaBy h z0 hl cv fh S F ev leg

/-! ## The paused run -/

/-- The whole system's state: every chain's manager and every chain's pause flags.  The tree
side is the fixed history `System`, as in `Contracts.Refund` and `Contracts.FlowBinding`. -/
structure PState where
  mgrs : Managers
  flags : Flags

/-- Write one leg's state on one chain's manager. -/
def PState.setLeg (Y : PState) (c : Chain) (f b : UInt256) (s : LegState) : PState :=
  ⟨setAt Y.mgrs c ((Y.mgrs c).set f b s), Y.flags⟩

/-- Write one pause flag. -/
def PState.setFlag (Y : PState) (c : Chain) (k : Pausable) (v : Bool) : PState :=
  ⟨Y.mgrs, Y.flags.set c k v⟩

/-- One step of the paused run, as it is recorded in the trace. -/
inductive Action where
  /-- `AtomicFlowManager.append(f, b, ..)` on chain `c`, inside `sendBundle`. -/
  | append (c : Chain) (f b : UInt256)
  /-- `executeAtomicBundle`, which runs `requireFlowFinalized` on the call `e`. -/
  | execute (e : ExecCall)
  /-- `authorizeRefund`, as logged by `ReachLog`. -/
  | authorize (a : AuthCall)
  /-- `claimRefund(f, bundle)` on chain `c`, for the bundle with hash `b`. -/
  | claim (c : Chain) (f b : UInt256)
  /-- The owner's `pause()` on chain `c`'s contract `k`. -/
  | pause (c : Chain) (k : Pausable)
  /-- The owner's `unpause()` on chain `c`'s contract `k`. -/
  | unpause (c : Chain) (k : Pausable)

/-- The calls of the trace that ran `_checkFlowId`, as `RunLog` logs them. -/
def Action.checked? : Action → Option CheckedCall
  | .execute e => some (.execute e)
  | .authorize a => some (.authorize a)
  | _ => none

/-- `RunLog`'s log of a trace: its `execute` and `authorize` steps, in order. -/
def checkedCalls (tr : List Action) : List CheckedCall := tr.filterMap Action.checked?

/-- **THE RUN, WITH PAUSE FLAGS.**  `PRun h z0 hl cv fh S prof X Y tr`: from `X` the system
reaches `Y` through the steps `tr`, most recent first.

The five protocol steps are `RunLog`'s, with the same guards, plus each one's pause gate:
`append` needs the send gate, `execute` the execution gate, and `claim` the refund gate.
`authorize` has none (`AtomicFlowManager.sol:134-162`).  `pause` and `unpause` are the owner's
`pause()` and `unpause()`.  Each carries OpenZeppelin's `whenNotPaused` or `whenPaused` and
writes only its flag. -/
inductive PRun (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (prof : Profile) : PState → PState → List Action → Prop
  | refl {X} : PRun h z0 hl cv fh S prof X X []
  | append {X Y tr c f b} : PRun h z0 hl cv fh S prof X Y tr → AppendGuard (Y.mgrs c) f b →
      SendOpen prof Y.flags c b →
      PRun h z0 hl cv fh S prof X (Y.setLeg c f b .Committed) (.append c f b :: tr)
  | execute {X Y tr} (e : ExecCall) : PRun h z0 hl cv fh S prof X Y tr →
      e.Verified h z0 hl cv fh S → ExecOpen prof Y.flags e.leg.bundleHash →
      PRun h z0 hl cv fh S prof X Y (.execute e :: tr)
  | authorize {X Y tr} (a : AuthCall) : PRun h z0 hl cv fh S prof X Y tr →
      a.Verified h z0 hl cv fh S →
      AuthorizeGuard (Y.mgrs a.leg.chain) a.flow.flowId a.leg.bundleHash →
      PRun h z0 hl cv fh S prof X (Y.setLeg a.leg.chain a.flow.flowId a.leg.bundleHash .Revertable)
        (.authorize a :: tr)
  | claim {X Y tr c f b} : PRun h z0 hl cv fh S prof X Y tr → ClaimGuard (Y.mgrs c) f b →
      RecoverOpen prof Y.flags c b →
      PRun h z0 hl cv fh S prof X (Y.setLeg c f b .Reverted) (.claim c f b :: tr)
  | pause {X Y tr c k} : PRun h z0 hl cv fh S prof X Y tr → Y.flags c k = false →
      PRun h z0 hl cv fh S prof X (Y.setFlag c k true) (.pause c k :: tr)
  | unpause {X Y tr c k} : PRun h z0 hl cv fh S prof X Y tr → Y.flags c k = true →
      PRun h z0 hl cv fh S prof X (Y.setFlag c k false) (.unpause c k :: tr)

/-! ## The run with each chain's tree attached

`Contracts.AppendPath.SysSteps` (`Specs/OncePerLeg.lean`) is the system run in which `append`
is the composed manager-and-tree step: the leg guard and the tree's `insert` of the commit
value, in one transaction.  `PSysSteps` adds the same gates and flag steps to it as `PRun`
adds to `RunLog`.  `SysSteps` has no execution step, so the execution gate does not appear. -/

/-- Every chain's manager and tree, and every chain's pause flags. -/
structure PSysState where
  chains : Contracts.AppendPath.Chains
  flags : Flags

/-- **THE TREE-ATTACHED SYSTEM RUN, WITH PAUSE FLAGS.**  `SysSteps`' five steps, with the send
gate on `append` and the refund gate on `claim`, and the owner's `pause`/`unpause` steps.  The
logs are `SysSteps`' logs: the appended obligations and the `authorizeRefund` calls, most
recent first. -/
inductive PSysSteps (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (prof : Profile) (X : PSysState) :
    PSysState → List Obligation → List AuthCall → Prop
  | refl : PSysSteps h z0 hl cv fh S prof X X [] []
  | append {Y log alog c f b hint low} : PSysSteps h z0 hl cv fh S prof X Y log alog →
      Contracts.AppendPath.AppendSucceeds cv (Y.chains c) f b hint low →
      SendOpen prof Y.flags c b →
      PSysSteps h z0 hl cv fh S prof X
        ⟨Y.chains.update c ((Y.chains c).appended cv f b low), Y.flags⟩ (⟨f, b, c⟩ :: log) alog
  | authorize {Y log alog} (a : AuthCall) : PSysSteps h z0 hl cv fh S prof X Y log alog →
      a.Verified h z0 hl cv fh S →
      AuthorizeGuard (Y.chains a.leg.chain).mgr a.flow.flowId a.leg.bundleHash →
      PSysSteps h z0 hl cv fh S prof X
        ⟨Y.chains.update a.leg.chain
          ⟨(Y.chains a.leg.chain).mgr.set a.flow.flowId a.leg.bundleHash .Revertable,
            (Y.chains a.leg.chain).tree⟩, Y.flags⟩
        log (a :: alog)
  | claim {Y log alog c f b} : PSysSteps h z0 hl cv fh S prof X Y log alog →
      ClaimGuard (Y.chains c).mgr f b → RecoverOpen prof Y.flags c b →
      PSysSteps h z0 hl cv fh S prof X
        ⟨Y.chains.update c ⟨(Y.chains c).mgr.set f b .Reverted, (Y.chains c).tree⟩, Y.flags⟩
        log alog
  | initL2 {Y log alog c} : PSysSteps h z0 hl cv fh S prof X Y log alog →
      (Y.chains c).tree.leafCount = 0 →
      PSysSteps h z0 hl cv fh S prof X
        ⟨Y.chains.update c ⟨(Y.chains c).mgr, Contracts.AppendPath.reseed (Y.chains c).tree⟩,
          Y.flags⟩ log alog
  | pause {Y log alog c k} : PSysSteps h z0 hl cv fh S prof X Y log alog → Y.flags c k = false →
      PSysSteps h z0 hl cv fh S prof X ⟨Y.chains, Y.flags.set c k true⟩ log alog
  | unpause {Y log alog c k} : PSysSteps h z0 hl cv fh S prof X Y log alog →
      Y.flags c k = true →
      PSysSteps h z0 hl cv fh S prof X ⟨Y.chains, Y.flags.set c k false⟩ log alog

/-! ## A flow whose legs are all committed in time, and the breaks its refund can rest on -/

/-- Every leg of `F` is committed by an on-time batch of its own declared source chain: the
leg's commit value is a key of that chain's tree at the end of some batch whose timestamp is
at or before `F`'s deadline. -/
def CommittedOnTime (cv : CommitValue) (S : System) (F : Flow) : Prop :=
  ∀ leg ∈ F.legs, ∃ n, S.time leg.chain n ≤ F.deadline ∧
    legValue cv F leg ∈ keys (toAbs (S.tree leg.chain n))

/-- **A LOCATED BREAK BEHIND A REFUND OF A COMMITTED FLOW'S OBLIGATION.**  Some
`authorizeRefund` call `a` in the log marked exactly obligation `o`, and either

* `fh` collides on the `(legs, deadline)` preimages of `F` and of `a`'s flow
  (`FlowIdClash`), or
* `a`'s flow is `F`, and `a`'s own absence proof carries a `TreeRootBreak` on the root its
  timeout branch selects (`AbsenceBreak`).

The other case of `Contracts.Refund.RefundBreak`, a break on an executed flow's inclusion proof,
cannot arise: commitment here is a fact about the history, not a verified proof. -/
def CommittedRefundBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) (fh : FlowHash) (S : System)
    (F : Flow) (o : Obligation) (log : List AuthCall) : Prop :=
  ∃ a ∈ log, obligationOf a.flow a.leg = o
    ∧ (FlowIdClash fh F a.flow
        ∨ (a.flow = F ∧ AbsenceBreak h z0 hl S F.deadline a.missing.chain a.batch a.proof))

/-! ## The witnesses' world

`mixedSystem 1`: chain `0` commits the value `1` in its first batch and chain `1` never commits.
Batch numbers are timestamps.  Under the commit value `fun _ _ => 1`, the one-leg flow
`subsetFlow 0 1` (leg `⟨0, 1⟩`, id `0`, deadline `0`) is committed in time.  The two-leg flow
`mixedFlow 1 1 2` (id `1`) has leg `⟨1, 2⟩` on the silent chain `1`, so it times out
(`Contracts.Refund.twoFlowCall`).  Both are checked by `lengthFlowHash`. -/

/-- The witnesses' profile: every bundle's destination is chain `7`, and every bundle goes
through the router and the vault on every path. -/
def vaultProfile : Profile where
  dest := fun _ => 7
  sendsViaRouter := fun _ => true
  burnsViaVault := fun _ => true
  mintsViaVault := fun _ => true
  recoversViaVault := fun _ => true

end Contracts.InteropPause
