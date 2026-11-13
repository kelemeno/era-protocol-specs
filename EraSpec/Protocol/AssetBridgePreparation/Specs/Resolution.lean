import EraSpec.Protocol.AssetBridgePreparation.Specs.Model
import EraSpec.Contracts.NativeTokenVaultBase.Specs.Resolution

/-!
# Resolution: delivery and refund close the preparation trace, across two chains

`Specs/Model.lean` is a closed trace of preparations and ordinary spending. It has no
resolution step, so it can only say that supply plus pending value is constant on ONE chain.
This file adds the two ways a pending entry is resolved, each on its own chain, and keeps both
chains' vaults in one state. Sources are cited at pin `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`
(`l1-contracts/contracts/`).

## The two chains and the steps

* `source` is the chain where entries are prepared and refunded; `destination` is the chain
  where they are delivered. Both are `NativeTokenVaultBase.State`s, each holding a bridged
  representation of the asset (the registered bridged branch on both sides).
* `prepare r`: a successful source preparation (`NativeTokenVaultBase.prepare`, the `bridgeBurn`
  branch of `NativeTokenVaultBase/Specs/RepresentationPreparation.lean`). The returned mint data,
  with the request's outer route context, is appended as one entry, exactly as `Step.prepare`
  in `Specs/Model.lean` does.
* `spendSource`, `spendDestination`: an ordinary successful token transfer on either chain
  (`BridgedStandardERC20.transfer`). Entries are unchanged.
* `deliver i wd`: the destination executes entry `i`. The deployed path is
  `L2InteropHandler.executeAtomicBundle` (`interop/interop-handler/L2InteropHandler.sol:49-100`),
  then the router's `receiveMessage` (`bridge/asset-router/AssetRouterBase.sol:215-256`, self-call
  at :247), `L2AssetRouter.finalizeDeposit` (`bridge/asset-router/L2AssetRouter.sol:265-274`) and
  `_finalizeDeposit` (`AssetRouterBase.sol:275-292`), which calls
  `bridgeMint(_sourceChainId, _assetId, _transferData)` on the vault (:284, :290). The model is
  `NativeTokenVaultBase.bridgeMint` (`NativeTokenVaultBase/Specs/Resolution.lean`) on the call
  `twoChainDeliveryCall`: the destination router as caller, no value, the source chain's id, and the
  entry's asset id and mint data verbatim.
* `refund i wr`: the source refunds entry `i`. The deployed path is
  `AtomicFlowManager.claimRefund` (`atomic-interop/AtomicFlowManager.sol:165-180`), then
  `_recoverBundle` (:219-230) and `L2AssetRouter.recoverAtomicCall` (`L2AssetRouter.sol:281-296`),
  which forwards the mint data verbatim to `bridgeRecoverFailedTransfer(_destChainId, assetId,
  mintData)` (:294). The model is `NativeTokenVaultBase.bridgeRecoverFailedTransfer` on the call
  `twoChainRefundCall`: the source router as caller, the burn's destination chain, and the entry's
  asset id and mint data verbatim. For an entry made by `prepare`, `twoChainRefundCall` is B2's
  `NativeTokenVaultBase.recoveryCall` (`Properties.TwoChainRefundCallIsRecoveryCall`).

## Two local records, no shared lock

The vault keeps no record of resolved data
(`NativeTokenVaultBase.Properties.VaultHasNoReplayGuard`). At-most-once resolution comes from
the callers, each on its own chain:

* `delivered` is the destination's record. The interop handler requires the bundle to be
  `Unreceived` and sets `bundleStatus[bundleHash] = FullyExecuted` before running any call
  (`L2InteropHandler.sol:79, 86`); the manager's header says the handler "owns the replay guard"
  (`AtomicFlowManager.sol:41-42`).
* `refunded` is the source's record. The manager requires the leg to be `Revertable` and flips
  it to `Reverted` before any recovery call (`AtomicFlowManager.sol:169-175`).

Each step reads only its own chain's record. The destination never reads `refunded` and the
source never reads `delivered`: in the deployed system the two records live on different
chains. Exclusivity of the two outcomes has to come from the evidence.

## Evidence

`ResolutionGate` is the cross-chain evidence each resolution consumes, as
`Applications.BurnMintBridge.Evidence` is for the reference bridge. `finalize i wd`: the
destination's witness `wd` (for instance the gate proofs submitted to `requireFlowFinalized`)
passes for entry `i`. `recover i wr`: the source's witness `wr` (for instance a manager run that
made the leg `Revertable`) passes for entry `i`. Both are predicates over the whole lifetime of
the system, so stale and later evidence is included. `Sound` says no entry has both.
`SoundOrBreak Brk` says that whenever both pass for one entry, `Brk` holds on exactly the two
submitted witnesses. `Specs/ResolutionEvidence.lean` instantiates the gate with the atomic
interop gate and refund path (`Protocol/InteropAtomicity`) and with the multichain refund gate
(`Protocol/MultichainGate`).

## Model boundaries

* Entry identity (`REP-PUBLISH`, `MODEL-TRACE`). The two records are keyed by the entry's
  position in the trace. The deployed records are keyed by bundle hash and by
  `(flowId, bundleHash)`. The model assumes each entry is published as exactly one bundle leg;
  a router that published the same burn twice is outside it.
* Branch. Delivery and refund are the vault's registered bridged branch (B2's
  `RegisteredBridged`). The destination router's handler for the asset is assumed to be the
  vault (`AssetRouterBase.sol:281-291`; custom handlers are `AssetRouterBase/AtomicRecovery`),
  and the first-bridge deploy branch is not a step here.
* Omitted reject-only checks: the handler's pause, source-chain, destination-chain, base-token
  and execution-address checks (`L2InteropHandler.sol:50, 57, 62-75`;
  `InteropHandlerBase.sol:428-450`), the router's sender and selector checks
  (`AssetRouterBase.sol:220-244`; `L2AssetRouter.sol:269-270, 284-287`), and the manager's
  `recovered != 0` check (`AtomicFlowManager.sol:229`). A check that only rejects removes runs,
  so the safety results below also hold with it. `Properties.TwoChainRefundAvailable` is
  enabledness in this model; in the deployed system those checks must pass as well.
* No other writers: pause and admin actions, registrations, other assets, other chains and the
  first-bridge branch are not steps (`OPS-CONFIG`).
* Rollback is the `Option` commit (`MODEL-COMMIT`). A failed delivery or refund is the absence
  of a step, so a retry after a revert is simply a later step of the same kind.

**This file is definitions only.** Statements: `../Properties/Resolution.lean`; proofs:
`../Proofs/Resolution.lean`.
-/

namespace AssetBridgePreparation

open Contracts

/-! ## Evidence -/

/-- **THE CROSS-CHAIN EVIDENCE A RESOLUTION CONSUMES.** `finalize i wd`: the destination's
witness `wd` passes the destination's gate for pending entry `i`. `recover i wr`: the source's
witness `wr` passes the source's refund path for entry `i`. Lifetime predicates: they do not
depend on the trace state or on when they are used. -/
structure ResolutionGate (Wd Wr : Type) where
  finalize : ℕ → Wd → Prop
  recover : ℕ → Wr → Prop

variable {Wd Wr : Type}

/-- **SOUND EVIDENCE.** No entry has both a passing destination witness and a passing source
witness, whatever the two witnesses are. -/
def ResolutionGate.Sound (G : ResolutionGate Wd Wr) : Prop :=
  ∀ (i : ℕ) (wd : Wd) (wr : Wr), ¬ (G.finalize i wd ∧ G.recover i wr)

/-- **SOUND UP TO A LOCATED BREAK.** Whenever a destination witness `wd` and a source witness `wr`
both pass for entry `i`, the break predicate `Brk` holds on exactly `i`, `wd` and `wr`. `Sound` is
the case `Brk = False`. -/
def ResolutionGate.SoundOrBreak (G : ResolutionGate Wd Wr) (Brk : ℕ → Wd → Wr → Prop) : Prop :=
  ∀ (i : ℕ) (wd : Wd) (wr : Wr), G.finalize i wd → G.recover i wr → Brk i wd wr

/-! ## State and environment -/

/-- The two chains' vaults and the trace's bookkeeping. `pending` and the two records are ghost
trace state: `pending` is not vault storage, and the records stand for the callers' replay state
on each chain (see the header). -/
structure TwoChainLedger (A B : Type) where
  /-- The source chain's vault: preparations burn here and refunds re-mint here. -/
  source : NativeTokenVaultBase.State A
  /-- The destination chain's vault: deliveries mint here. -/
  destination : NativeTokenVaultBase.State B
  /-- Every prepared entry, in preparation order. Entries are never removed or rewritten. -/
  pending : List Obligation
  /-- The destination's record: positions of the entries it has executed. -/
  delivered : Finset ℕ
  /-- The source's record: positions of the entries it has refunded. -/
  refunded : Finset ℕ

/-- The fixed dependencies of a run: the source's preparation hooks (`_handleBridgeToChain`,
metadata), the source's and the destination's resolution hook (`_handleBridgeFromChain`), and the
evidence. Hooks are parameters, as in B2 (`DEP-FRAME`, `DEP-RESULTS`). -/
structure TwoChainEnv (A B Wd Wr : Type) where
  hooks : NativeTokenVaultBase.Hooks A
  sourceResolve : NativeTokenVaultBase.ResolutionHooks A
  destinationResolve : NativeTokenVaultBase.ResolutionHooks B
  gate : ResolutionGate Wd Wr

/-- The vault call a destination delivery makes for entry `o`: `bridgeMint(_sourceChainId,
_assetId, _transferData)` from the destination's router (`AssetRouterBase.sol:284, 290`), with no
value (atomic legs carry none: `AtomicFlowManager.sol:217-218`), the chain the message came from,
and the entry's asset id and mint data verbatim. -/
def twoChainDeliveryCall (router : NativeTokenVaultBase.Address) (sourceChain : UInt256)
    (o : Obligation) : NativeTokenVaultBase.ResolutionCall :=
  ⟨router, 0, sourceChain, o.assetId, o.data⟩

/-- The vault call a source refund makes for entry `o`: `bridgeRecoverFailedTransfer(_destChainId,
assetId, mintData)` from the source's router (`L2AssetRouter.sol:294`), with no value, the burn's
destination chain, and the entry's asset id and mint data verbatim. -/
def twoChainRefundCall (router : NativeTokenVaultBase.Address) (o : Obligation) :
    NativeTokenVaultBase.ResolutionCall :=
  ⟨router, 0, o.destinationChain, o.assetId, o.data⟩

/-- One trace step, labelled. Resolution labels carry the position of the entry and the witness
the step consumed, so a run's label list is its own log. -/
inductive TwoChainLabel (Wd Wr : Type) where
  | prepare (r : NativeTokenVaultBase.Request)
  | spendSource
  | spendDestination
  | deliver (i : ℕ) (wd : Wd)
  | refund (i : ℕ) (wr : Wr)

variable {A B : Type}

/-- **THE TWO-CHAIN TRACE.** Preparation and spending as in `Step`; a delivery and a refund each
consume one entry on its own chain, guarded only by that chain's own record and by the evidence,
and succeed only if the modelled vault call succeeds. -/
inductive TwoChainStep (E : TwoChainEnv A B Wd Wr) :
    TwoChainLedger A B → TwoChainLabel Wd Wr → TwoChainLedger A B → Prop
  | prepare {s : TwoChainLedger A B} {r : NativeTokenVaultBase.Request}
      {out : NativeTokenVaultBase.Result A} :
      NativeTokenVaultBase.prepare E.hooks s.source r = some out →
      TwoChainStep E s (.prepare r)
        { s with source := out.state, pending := s.pending ++ [obligation r out.data] }
  | spendSource {s : TwoChainLedger A B} {owner recipient : NativeTokenVaultBase.Address}
      {amount : UInt256} {token : BridgedStandardERC20.State} :
      BridgedStandardERC20.transfer s.source.token owner recipient amount = some token →
      TwoChainStep E s .spendSource { s with source := { s.source with token := token } }
  | spendDestination {s : TwoChainLedger A B} {owner recipient : NativeTokenVaultBase.Address}
      {amount : UInt256} {token : BridgedStandardERC20.State} :
      BridgedStandardERC20.transfer s.destination.token owner recipient amount = some token →
      TwoChainStep E s .spendDestination
        { s with destination := { s.destination with token := token } }
  | deliver {s : TwoChainLedger A B} {i : ℕ} {o : Obligation} {wd : Wd}
      {d : NativeTokenVaultBase.State B} :
      s.pending[i]? = some o → i ∉ s.delivered → E.gate.finalize i wd →
      NativeTokenVaultBase.bridgeMint E.destinationResolve s.destination
          (twoChainDeliveryCall s.destination.config.router s.source.config.chainId o) = some d →
      TwoChainStep E s (.deliver i wd)
        { s with destination := d, delivered := insert i s.delivered }
  | refund {s : TwoChainLedger A B} {i : ℕ} {o : Obligation} {wr : Wr}
      {u : NativeTokenVaultBase.State A} :
      s.pending[i]? = some o → i ∉ s.refunded → E.gate.recover i wr →
      NativeTokenVaultBase.bridgeRecoverFailedTransfer E.sourceResolve s.source
          (twoChainRefundCall s.source.config.router o) = some u →
      TwoChainStep E s (.refund i wr)
        { s with source := u, refunded := insert i s.refunded }

/-- Runs, with their labels in order. -/
inductive TwoChainRun (E : TwoChainEnv A B Wd Wr) :
    TwoChainLedger A B → List (TwoChainLabel Wd Wr) → TwoChainLedger A B → Prop
  | refl {s : TwoChainLedger A B} : TwoChainRun E s [] s
  | tail {s t u : TwoChainLedger A B} {ls : List (TwoChainLabel Wd Wr)}
      {l : TwoChainLabel Wd Wr} :
      TwoChainRun E s ls t → TwoChainStep E t l u → TwoChainRun E s (ls ++ [l]) u

/-! ## The trace without the local records, for a countermodel -/

/-- **THE TRACE WITHOUT THE TWO LOCAL REPLAY GUARDS**, for the countermodel
`Properties.TwoChainWithoutRecordsPaysTwice` only: every step of `TwoChainStep`, plus a delivery
that does not check the destination's record (the handler without its `Unreceived` check,
`L2InteropHandler.sol:79`) and a refund that does not check the source's record (the manager
without its `Revertable` check, `AtomicFlowManager.sol:169-170`). -/
inductive TwoChainStepUnguarded (E : TwoChainEnv A B Wd Wr) :
    TwoChainLedger A B → TwoChainLabel Wd Wr → TwoChainLedger A B → Prop
  | guarded {s : TwoChainLedger A B} {l : TwoChainLabel Wd Wr} {t : TwoChainLedger A B} :
      TwoChainStep E s l t → TwoChainStepUnguarded E s l t
  | redeliver {s : TwoChainLedger A B} {i : ℕ} {o : Obligation} {wd : Wd}
      {d : NativeTokenVaultBase.State B} :
      s.pending[i]? = some o → E.gate.finalize i wd →
      NativeTokenVaultBase.bridgeMint E.destinationResolve s.destination
          (twoChainDeliveryCall s.destination.config.router s.source.config.chainId o) = some d →
      TwoChainStepUnguarded E s (.deliver i wd)
        { s with destination := d, delivered := insert i s.delivered }
  | rerefund {s : TwoChainLedger A B} {i : ℕ} {o : Obligation} {wr : Wr}
      {u : NativeTokenVaultBase.State A} :
      s.pending[i]? = some o → E.gate.recover i wr →
      NativeTokenVaultBase.bridgeRecoverFailedTransfer E.sourceResolve s.source
          (twoChainRefundCall s.source.config.router o) = some u →
      TwoChainStepUnguarded E s (.refund i wr)
        { s with source := u, refunded := insert i s.refunded }

/-- Runs of the trace without the local records. -/
inductive TwoChainRunUnguarded (E : TwoChainEnv A B Wd Wr) :
    TwoChainLedger A B → List (TwoChainLabel Wd Wr) → TwoChainLedger A B → Prop
  | refl {s : TwoChainLedger A B} : TwoChainRunUnguarded E s [] s
  | tail {s t u : TwoChainLedger A B} {ls : List (TwoChainLabel Wd Wr)}
      {l : TwoChainLabel Wd Wr} :
      TwoChainRunUnguarded E s ls t → TwoChainStepUnguarded E t l u →
        TwoChainRunUnguarded E s (ls ++ [l]) u

/-! ## Accounting -/

/-- The amount of entry `i` (`0` past the end). -/
def pendingAmountAt (pending : List Obligation) (i : ℕ) : ℕ :=
  match pending[i]? with
  | some o => o.data.amount.val
  | none => 0

/-- The two representations' total supplies. -/
def TwoChainLedger.circulating (s : TwoChainLedger A B) : ℕ :=
  s.source.token.totalSupply + s.destination.token.totalSupply

/-- **VALUE IN FLIGHT.** The total amount of the entries that are neither delivered nor refunded. -/
def TwoChainLedger.outstanding (s : TwoChainLedger A B) : ℕ :=
  ∑ i ∈ Finset.range s.pending.length with i ∉ s.delivered ∧ i ∉ s.refunded,
    pendingAmountAt s.pending i

/-- **VALUE PAID TWICE.** The total amount of the entries that are both delivered and refunded. -/
def TwoChainLedger.doublePaid (s : TwoChainLedger A B) : ℕ :=
  ∑ i ∈ s.delivered ∩ s.refunded, pendingAmountAt s.pending i

/-- The source's own view: the total amount it burned and has not refunded. -/
def TwoChainLedger.unrefunded (s : TwoChainLedger A B) : ℕ :=
  ∑ i ∈ Finset.range s.pending.length with i ∉ s.refunded, pendingAmountAt s.pending i

/-- The destination's own view: the total amount it delivered. -/
def TwoChainLedger.deliveredAmount (s : TwoChainLedger A B) : ℕ :=
  ∑ i ∈ s.delivered, pendingAmountAt s.pending i

/-- Both records name existing entries only. -/
def TwoChainLedger.RecordsInRange (s : TwoChainLedger A B) : Prop :=
  (∀ i ∈ s.delivered, i < s.pending.length) ∧ (∀ i ∈ s.refunded, i < s.pending.length)

/-- No entry has been resolved yet on either chain; entries may already be pending. -/
def TwoChainLedger.FreshRecords (s : TwoChainLedger A B) : Prop :=
  s.delivered = ∅ ∧ s.refunded = ∅

/-- The trace has not started: no entry, no record. -/
def TwoChainLedger.FreshTrace (s : TwoChainLedger A B) : Prop :=
  s.pending = [] ∧ s.FreshRecords

/-! ## Counting resolutions in a run -/

/-- The entry a delivery label resolves. -/
def TwoChainLabel.deliveryOf : TwoChainLabel Wd Wr → Option ℕ
  | .deliver i _ => some i
  | _ => none

/-- The entry a refund label resolves. -/
def TwoChainLabel.refundOf : TwoChainLabel Wd Wr → Option ℕ
  | .refund i _ => some i
  | _ => none

/-- How many deliveries of entry `i` the labels contain. -/
def deliveryCount (ls : List (TwoChainLabel Wd Wr)) (i : ℕ) : ℕ :=
  ls.countP fun l => decide (l.deliveryOf = some i)

/-- How many refunds of entry `i` the labels contain. -/
def refundCount (ls : List (TwoChainLabel Wd Wr)) (i : ℕ) : ℕ :=
  ls.countP fun l => decide (l.refundOf = some i)

/-! ## Gates for the countermodel and the witnesses -/

/-- Evidence that accepts every witness on both sides: the unsound gate of the countermodel,
as `Applications.BurnMintBridge.conflictingEvidence`. -/
def acceptAllResolutionGate : ResolutionGate Unit Unit := ⟨fun _ _ => True, fun _ _ => True⟩

/-- Evidence that lets the destination execute entry `d` and the source refund entry `r`, and
nothing else. Sound when `d ≠ r`. -/
def splitResolutionGate (d r : ℕ) : ResolutionGate Unit Unit := ⟨fun i _ => i = d, fun i _ => i = r⟩

end AssetBridgePreparation
