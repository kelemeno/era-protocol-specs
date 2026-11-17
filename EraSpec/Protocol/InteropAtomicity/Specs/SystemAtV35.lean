import EraSpec.Protocol.InteropAtomicity.Specs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg
import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachine

/-!
# Model at `draft/v0.35.0`: every chain's atomic-interop storage, with the v35 entry points

**Commit.** matter-labs/era-contracts, branch `draft/v0.35.0` at
`d9f678900e1bc8286412b78f56d4a9f443983c29`.  Paths are relative to `l1-contracts/contracts/`
unless they start with `protocol-docs/`.  Every other model in this folder describes the pinned
tree `c67894b9`; none of them is changed here.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.SystemAtV35`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.SystemAtV35`.

## Why one composed model

At the pin the folder has three system relations: `Contracts.Refund.ReachLog` (managers only),
`Contracts.FlowBinding.RunLog` (managers and gate calls) and `Contracts.AppendPath.SysSteps`
(managers and trees).  At v35 the entry points those relations model read four more pieces of
state, each owned by another contract:

| v35 check | state it reads | where |
|---|---|---|
| receive filter in `requireFlowFinalized` / `authorizeRefund` | `L2Bridgehub.isPeerAllowed` | `AtomicFlowManager.sol:201, :231, :338-344`; `core/bridgehub/L2Bridgehub.sol:43` |
| registration of the other legs' sources in `append` | `L2Bridgehub.baseTokenAssetId` | `AtomicFlowManager.sol:152-160` |
| send-side destination allowlist | both of the above | `interop/InteropCenter.sol:629-631, :696-704` |
| expired-flow gate in `append` | `L2InteropRootStorage.latestInteropRootTimestamp` | `AtomicFlowManager.sol:120-125`; `interop/L2InteropRootStorage.sol:36, :98-100` |
| imported root after the deadline in `authorizeRefund` | `L2InteropRootStorage.interopRoots` | `atomic-interop/libraries/AtomicInteropProof.sol:94-100` |
| verify, then execute or unbundle, without a second gate | `InteropHandlerBase.bundleStatus` | `interop/interop-handler/L2InteropHandler.sol:61-92`; `InteropHandlerBase.sol:55` |

and the tree's `insert` walks from a stale hint without a hop bound
(`common/libraries/IndexedMerkleTree.sol:90-93`).  `RunV35` below is one relation over all of
it, so that the ordering facts between these pieces (an `authorizeRefund` on chain `X` before an
`append` on `X`; a `verifyAtomicBundle` before a deregistration) can be stated at all.

## The state, per chain

* `base` — the pin's `ChainState`: the flow manager's `_state` (`AtomicFlowManager.sol:61`) and
  the commitment tree's list state (`L2InteropCommitmentTree.sol:31`;
  `IndexedMerkleTree.sol:30-34`).
* `hub` — the two `L2Bridgehub` entries per peer chain the atomic path reads: `isPeerAllowed`
  and whether `baseTokenAssetId` is nonzero.
* `roots` — the settlement-layer (L1) half of `L2InteropRootStorage`: the timestamp imported at
  each settlement-layer batch (`0` = not imported) and the running maximum.  The settlement
  layer is pinned to L1 by `_checkSettlementLayerIsL1` (`AtomicFlowManager.sol:329-333`), so one
  settlement layer suffices.
* `status` — `InteropHandlerBase.bundleStatus` (`InteropHandlerBase.sol:55`), per bundle hash.

## The steps, and what each one models

* `append` — `InteropCenter._sendBundle` → `_dispatchBundle` → `AtomicFlowManager.append`
  (`InteropCenter.sol:533-613, :727-750`; `AtomicFlowManager.sol:104-173`).  Every check of
  `append` is a field of `AppendOkV35`, plus the send-side destination check.  The tree insert
  is `InsertOkV35`: the pin's `InsertSucceeds` with the unbounded walk.
* `importRoot` — `L2InteropRootStorage._addInteropRoot` (`L2InteropRootStorage.sol:70-103`).
* `gate` — `verifyAtomicBundle` (`L2InteropHandler.sol:83-92`, to `Verified`) or
  `executeAtomicBundle` on an `Unreceived` bundle (`:61-78`, to `FullyExecuted`): both run
  `requireFlowFinalized` (`AtomicFlowManager.sol:176-213`), here `GateOkV35`.
* `resume` — the two status edges that run NO gate: `executeAtomicBundle` on a `Verified`
  bundle (`L2InteropHandler.sol:73-77`) and `unbundleBundle` (`InteropHandlerBase.sol:113-175`).
* `authorize` — `authorizeRefund` (`AtomicFlowManager.sol:216-247`), one marked leg per step,
  on the leg's declared chain, as in the pin's `ReachLog` (see "What is not modelled").
* `claim` — `claimRefund` (`AtomicFlowManager.sol:250-265`).
* `admin` — `L2Bridgehub.allowInteropPeer` (`L2Bridgehub.sol:95-99`),
  `deregisterChainForInterop` (`:102-105`), and the writers of `baseTokenAssetId` that do not
  set `isPeerAllowed` (`core/bridgehub/BridgehubBase.sol:447` and pre-v35 registrations,
  `protocol-docs/interop-gating.md:201-210`).  Enabled for every pair at every moment.
* `initL2` — `L2InteropCommitmentTree.initL2` (`L2InteropCommitmentTree.sol:45-48`).  At v35
  it runs only in the genesis upgrade (`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:230-231,
  :373`); the step is kept, with the pin's `leafCount = 0` guard, as an over-approximation.

The log records every `append`, every gate call, every `authorizeRefund` and every admin step,
most recent first.

## What is not modelled

* `authorizeRefund` marks every `Committed` leg of the presented flow in the CALLING chain's
  manager (`AtomicFlowManager.sol:238-246`), whatever chain the flow declares for it.  Like the
  pin's `ReachLog`, `authorize` marks a leg on its declared chain.  At `main` (identical code)
  the binding topic proves the two agree up to a logged flow-id clash
  (`Contracts.FlowBindingAtHead.Properties.AuthorizeMarksDeclaredLegOrLoggedClash`, other
  workflow); that argument applies verbatim at v35.
* The flow preimage's `version` byte and settlement-layer field (`IAtomicInterop.sol:50-56`)
  are constants folded into `FlowHash`, as at the pin.
* The handler's pause, execution-address and unbundler-address checks, the destination base
  token check and the per-call statuses (`InteropHandlerBase.sol:113-175, :239-300, :390-410`):
  they only reject.  The per-call machine is `EraSpec.Protocol.DestinationCapstoneAtV35`.
* Who may send admin steps (`ChainRegistrationSender.sol:77-119`, `onlyChainRegistrationSender`
  at `L2Bridgehub.sol:45-53`) and the service-transaction delay.
* The tree side of every proof is the fixed history `S`, exactly as at the pin.  The imported
  roots in `roots` carry only their timestamps; which root a proof authenticates against stays
  inside `S`.
-/

namespace Contracts.SystemAtV35

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.FlowBinding Contracts.AppendPath

/-- `InteropHandlerBase.BundleStatus` (`interop/interop-handler/InteropHandlerBase.sol:55`), as
modelled at the pin by `AttackVectors.BundleStatusMachine.Status`. -/
abbrev BundleStatus := AttackVectors.BundleStatusMachine.Status

/-! ## The tree's insert, with the unbounded walk -/

/-- **`IndexedMerkleTree.insert(v, hint)` SUCCEEDS AT v35, LANDING ON LOW LEAF `low`**
(`common/libraries/IndexedMerkleTree.sol:65-107`).  The fields are the checks in source order.
`walk` is the deployed loop

    while (lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value) {   // :90
        lowLeafIndex = lowLeaf.nextIndex;                              // :91
        lowLeaf = self.leaves[lowLeafIndex];                           // :92
    }

which has no hop bound at v35 (#2349): it exits at `low` after some number of hops.  The pin's
`InsertSucceeds` is the same structure with the walk cut at `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5`
hops (`lowSearch … maxLowIndexSearchAttempts`).  The writes (`:95-106`) are the pin's
`Contracts.InteropCommitmentTree.insert T v low`. -/
structure InsertOkV35 (T : Tree) (v : UInt256) (hint low : ℕ) : Prop where
  /-- `IMTNotInitialized` (`:71-73`). -/
  initialized : Initialized T
  /-- `IMTValueZero` (`:74-76`). -/
  nonzero : v ≠ 0
  /-- `IMTValueAlreadyExists` (`:77-79`): the dedup gate. -/
  fresh : T.valueToIndex v = 0
  /-- `IMTLowLeafIndexOutOfBounds` (`:80-82`). -/
  hintInBounds : hint < T.leafCount
  /-- `IMTLowLeafValueTooLarge` (`:85-88`). -/
  hintBelow : (T.leaf hint).value < v
  /-- The unbounded walk (`:90-93`) exits at `low`. -/
  walk : ∃ hops : ℕ, lowSearch T v hops hint = some low

/-! ## The other contracts' state the atomic path reads -/

/-- One chain's `L2Bridgehub` entries for every peer chain `s`: `peer s` is
`isPeerAllowed[s]` (`core/bridgehub/L2Bridgehub.sol:43`), and `registered s` is
`baseTokenAssetId[s] != bytes32(0)`. -/
structure Hub where
  peer : Chain → Bool
  registered : Chain → Bool

/-- **`_checkLegSourceAllowed(s)` PASSES ON CHAIN `c`** (`AtomicFlowManager.sol:338-344`): `s` is
`block.chainid`, or `c`'s bridgehub allows `s`. -/
def SourceAllowed (H : Hub) (c s : Chain) : Prop := s = c ∨ H.peer s = true

instance (H : Hub) (c s : Chain) : Decidable (SourceAllowed H c s) := by
  unfold SourceAllowed; infer_instance

/-- An admin step on one chain's bridgehub. -/
inductive AdminOp where
  /-- `L2Bridgehub.allowInteropPeer(s, assetId)` (`L2Bridgehub.sol:95-99`): writes a nonzero
  `baseTokenAssetId[s]` (`:96-97`) and `isPeerAllowed[s] = true` (`:98`). -/
  | allow (s : Chain)
  /-- `L2Bridgehub.deregisterChainForInterop(s)` (`L2Bridgehub.sol:102-105`): deletes both. -/
  | deregister (s : Chain)
  /-- A write of a nonzero `baseTokenAssetId[s]` that leaves `isPeerAllowed[s]` alone: the
  settlement-layer migration path (`core/bridgehub/BridgehubBase.sol:447`) and registrations
  made before v35 (`protocol-docs/interop-gating.md:201-210`). -/
  | registerLegacy (s : Chain)

/-- The bridgehub after the admin step. -/
def AdminOp.apply : AdminOp → Hub → Hub
  | .allow s, H => ⟨fun x => if x = s then true else H.peer x,
      fun x => if x = s then true else H.registered x⟩
  | .deregister s, H => ⟨fun x => if x = s then false else H.peer x,
      fun x => if x = s then false else H.registered x⟩
  | .registerLegacy s, H => ⟨H.peer, fun x => if x = s then true else H.registered x⟩

/-- The settlement-layer (L1) half of one chain's `L2InteropRootStorage`: `stored blk` is
`storedInteropRoots[L1][blk].timestamp` (`interop/L2InteropRootStorage.sol:32, :39-44`; `0`
means nothing was imported at `blk`), and `latest` is `latestInteropRootTimestamp[L1]`
(`:36`). -/
structure Roots where
  stored : ℕ → ℕ
  latest : ℕ

/-- `_addInteropRoot(L1, blk, t, _)` (`L2InteropRootStorage.sol:70-103`): store the timestamp
(`:93`) and keep the maximum (`:98-100`). -/
def Roots.import (R : Roots) (blk t : ℕ) : Roots :=
  ⟨fun x => if x = blk then t else R.stored x, max R.latest t⟩

/-! ## Per-chain state and the world -/

/-- One chain's atomic-interop storage at v35. -/
structure ChainV35 where
  /-- The flow manager's `_state` and the commitment tree's list state (the pin's
  `ChainState`). -/
  base : ChainState
  /-- The bridgehub entries the atomic path reads. -/
  hub : Hub
  /-- The imported settlement-layer roots' timestamps. -/
  roots : Roots
  /-- `InteropHandlerBase.bundleStatus`. -/
  status : UInt256 → BundleStatus

/-- Every chain's state. -/
abbrev WorldV35 := Chain → ChainV35

/-- Replace one chain's state. -/
def WorldV35.set (W : WorldV35) (c : Chain) (x : ChainV35) : WorldV35 :=
  fun y => if y = c then x else W y

/-- The pin's view: every chain's manager and tree. -/
def WorldV35.chains (W : WorldV35) : Chains := fun c => (W c).base

/-- The pin's view: every chain's manager. -/
def WorldV35.mgrs (W : WorldV35) : Managers := fun c => (W c).base.mgr

/-- One bundle's status updated. -/
def setStatus (st : UInt256 → BundleStatus) (b : UInt256) (s : BundleStatus) :
    UInt256 → BundleStatus :=
  fun b' => if b' = b then s else st b'

/-- **GENESIS AT v35.**  Every chain after the genesis upgrade: the pin's `genesis` (empty manager,
`setup` tree), nothing imported, every bundle `Unreceived`, and the bridgehub in any state `H0 c`
(registrations predate the atomic path). -/
def genesisV35 (H0 : Chain → Hub) : WorldV35 :=
  fun c => ⟨genesis, H0 c, ⟨fun _ => 0, 0⟩, fun _ => .Unreceived⟩

/-! ## The entry points' checks -/

/-- `MAX_ATOMIC_FLOW_LEGS` (`atomic-interop/IAtomicInterop.sol:99`). -/
def maxAtomicFlowLegs : ℕ := 8

/-- **`append(b, hint, F)` SUCCEEDS ON CHAIN `c` AT v35, THE TREE LANDING ON `low`**, as reached
from `InteropCenter._sendBundle` (`interop/InteropCenter.sol:533-613`).  `dst b` is the bundle's
destination chain.  The fields are the checks in call order. -/
structure AppendOkV35 (cv : CommitValue) (fh : FlowHash) (dst : UInt256 → Chain) (x : ChainV35)
    (c : Chain) (F : Flow) (b : UInt256) (hint low : ℕ) : Prop where
  /-- `DestinationChainNotRegistered` (`InteropCenter.sol:697-698`, via `_buildInteropBundle`
  `:629-631`). -/
  destRegistered : x.hub.registered (dst b) = true
  /-- `DestinationChainNotAllowed` (`InteropCenter.sol:699-702`): the send-side allowlist.  Not on
  `main`. -/
  destAllowed : x.hub.peer (dst b) = true
  /-- `_validateAndComputeFlowId` (`AtomicFlowManager.sol:109`, `:360-379`): the flow id is the
  hash of the preimage (`:378`). -/
  flowId : FlowIdChecked fh F
  /-- `ManagerTooManyLegs` (`:367-369`). -/
  legCap : F.legs.length ≤ maxAtomicFlowLegs
  /-- `ManagerBundleHashesNotSorted` (`:370-374`): strictly ascending bundle hashes. -/
  sorted : (F.legs.map FlowLeg.bundleHash).Pairwise (· < ·)
  /-- `ManagerFlowDeadlinePassed` (`:120-125`): the expired-flow gate. -/
  notExpired : x.roots.latest ≤ F.deadline
  /-- `ManagerCommittedBundleNotInFlow` and `ManagerCommittedLegSourceChainMismatch`
  (`:130-147`).  With `sorted`, the first index carrying `b` is the only one, so "it declares this
  chain" is membership of `⟨c, b⟩`. -/
  isLegHere : (⟨c, b⟩ : FlowLeg) ∈ F.legs
  /-- `ManagerLegSourceChainNotRegistered` (`:152-160`). -/
  othersRegistered : ∀ l ∈ F.legs, l.chain ≠ c → x.hub.registered l.chain = true
  /-- `ManagerLegAlreadyCommitted` (`:162-164`). -/
  legUnset : AppendGuard x.base.mgr F.flowId b
  /-- The tree's `insert(commitValue(flowId, b), hint)` (`:168-170`;
  `L2InteropCommitmentTree.sol:51-64`). -/
  treeInsert : InsertOkV35 x.base.tree (cv F.flowId b) hint low

/-- **`requireFlowFinalized` PASSES ON CHAIN `d` AT v35** (`AtomicFlowManager.sol:176-213`) for
the logged call `e`: the pin's checks on the call's own evidence (`ExecCall.Verified`:
`_checkFlowId` `:182`, the inclusion proof of every leg `:194-209`, membership of the executing
bundle `:210-212`), and the receive filter on every leg's source (`:201`). -/
def GateOkV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (x : ChainV35) (d : Chain) (e : ExecCall) : Prop :=
  e.Verified h z0 hl cv fh S ∧ ∀ l ∈ e.flow.legs, SourceAllowed x.hub d l.chain

/-- **`authorizeRefund` PASSES ON THE LEG'S CHAIN AT v35** (`AtomicFlowManager.sol:216-247`), for
the logged call `a`, read on `x`, the state of chain `a.leg.chain`: the pin's checks
(`AuthCall.Verified`: `_checkFlowId` `:217`, the missing leg in the flow `:224-226`, the proof
bound to its declared chain `:227-230`, `verifyTimeoutAbsence` `:233-234`), the receive filter on
the missing leg's source (`:231`), and the imported settlement-layer root the absence proof was
authenticated against, created after the deadline (`AtomicInteropProof.sol:94-100`:
`ProofSettlementLayerInteropRootNotImported`, `ProofInteropRootNotAfterDeadline`). -/
def AuthorizeOkV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (x : ChainV35) (a : AuthCall) : Prop :=
  a.Verified h z0 hl cv fh S ∧ SourceAllowed x.hub a.leg.chain a.missing.chain
    ∧ ∃ blk, a.flow.deadline < x.roots.stored blk

/-- The status edges that run no gate. -/
inductive NoGateEdge : BundleStatus → BundleStatus → Prop
  /-- `executeAtomicBundle` on a `Verified` bundle skips `requireFlowFinalized`
  (`L2InteropHandler.sol:73-75`) and marks it `FullyExecuted` (`:77`;
  `InteropHandlerBase.sol:325-342`). -/
  | execute : NoGateEdge .Verified .FullyExecuted
  /-- `unbundleBundle` (`InteropHandlerBase.sol:139, :147`). -/
  | unbundleFirst : NoGateEdge .Verified .Unbundled
  /-- `unbundleBundle` again (`:139, :147`). -/
  | unbundleAgain : NoGateEdge .Unbundled .Unbundled

/-! ## The calls and the run -/

/-- One logged call of a v35 run. -/
inductive CallV35 where
  /-- `append(b, _, F)` succeeded on chain `c`. -/
  | append (c : Chain) (F : Flow) (b : UInt256)
  /-- `requireFlowFinalized` passed on chain `d` for `e` (from `verifyAtomicBundle`, or from
  `executeAtomicBundle` on an `Unreceived` bundle). -/
  | gate (d : Chain) (e : ExecCall)
  /-- `authorizeRefund` passed for `a`, on chain `a.leg.chain`. -/
  | authorize (a : AuthCall)
  /-- An admin step on chain `c`'s bridgehub. -/
  | admin (c : Chain) (op : AdminOp)

/-- **EVERY INTERLEAVING OF EVERY CHAIN'S ATOMIC-INTEROP CALLS AT v35, LOGGED.**
`RunV35 h z0 hl cv fh S dst X Y log`: from `X` the chains reach `Y`; `log` lists the calls, most
recent first.  `dst b` is the destination chain of the bundle with hash `b`. -/
inductive RunV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (dst : UInt256 → Chain) (X : WorldV35) : WorldV35 → List CallV35 → Prop
  | refl : RunV35 h z0 hl cv fh S dst X X []
  /-- `InteropCenter._sendBundle` → `AtomicFlowManager.append` on chain `c`. -/
  | append {Y log c F b hint low} : RunV35 h z0 hl cv fh S dst X Y log →
      AppendOkV35 cv fh dst (Y c) c F b hint low →
      RunV35 h z0 hl cv fh S dst X
        (Y.set c { Y c with base := (Y c).base.appended cv F.flowId b low })
        (.append c F b :: log)
  /-- `L2InteropRootStorage._addInteropRoot(L1, blk, t, _)` on chain `c`
  (`InteropRootTimestampIsZero` `:85-87`; `InteropRootAlreadyExists` `:89-91`, read here as
  "nothing imported at `blk`"). -/
  | importRoot {Y log c blk t} : RunV35 h z0 hl cv fh S dst X Y log → 0 < t →
      (Y c).roots.stored blk = 0 →
      RunV35 h z0 hl cv fh S dst X (Y.set c { Y c with roots := (Y c).roots.import blk t }) log
  /-- `verifyAtomicBundle` (to `Verified`) or `executeAtomicBundle` on an `Unreceived` bundle (to
  `FullyExecuted`) on chain `d`: the destination check (`InteropHandlerBase.sol:400-403`), the
  status check (`:313`, `:282-287`) and the gate. -/
  | gate {Y log d e st} : RunV35 h z0 hl cv fh S dst X Y log →
      dst e.leg.bundleHash = d → (Y d).status e.leg.bundleHash = .Unreceived →
      (st = .Verified ∨ st = .FullyExecuted) → GateOkV35 h z0 hl cv fh S (Y d) d e →
      RunV35 h z0 hl cv fh S dst X
        (Y.set d { Y d with status := setStatus (Y d).status e.leg.bundleHash st })
        (.gate d e :: log)
  /-- A status edge that runs no gate, on chain `d`. -/
  | resume {Y log d b st'} : RunV35 h z0 hl cv fh S dst X Y log →
      NoGateEdge ((Y d).status b) st' →
      RunV35 h z0 hl cv fh S dst X (Y.set d { Y d with status := setStatus (Y d).status b st' }) log
  /-- `authorizeRefund`, marking the leg `a.leg` of the checked flow `a.flow` on its chain. -/
  | authorize {Y log} (a : AuthCall) : RunV35 h z0 hl cv fh S dst X Y log →
      AuthorizeOkV35 h z0 hl cv fh S (Y a.leg.chain) a →
      AuthorizeGuard (Y a.leg.chain).base.mgr a.flow.flowId a.leg.bundleHash →
      RunV35 h z0 hl cv fh S dst X
        (Y.set a.leg.chain { Y a.leg.chain with
          base := ⟨(Y a.leg.chain).base.mgr.set a.flow.flowId a.leg.bundleHash .Revertable,
            (Y a.leg.chain).base.tree⟩ })
        (.authorize a :: log)
  /-- `claimRefund` on chain `c`. -/
  | claim {Y log c f b} : RunV35 h z0 hl cv fh S dst X Y log →
      ClaimGuard (Y c).base.mgr f b →
      RunV35 h z0 hl cv fh S dst X
        (Y.set c { Y c with base := ⟨(Y c).base.mgr.set f b .Reverted, (Y c).base.tree⟩ }) log
  /-- An admin step on chain `c`'s bridgehub. -/
  | admin {Y log} (c : Chain) (op : AdminOp) : RunV35 h z0 hl cv fh S dst X Y log →
      RunV35 h z0 hl cv fh S dst X (Y.set c { Y c with hub := op.apply (Y c).hub })
        (.admin c op :: log)
  /-- `L2InteropCommitmentTree.initL2` on chain `c`. -/
  | initL2 {Y log c} : RunV35 h z0 hl cv fh S dst X Y log →
      (Y c).base.tree.leafCount = 0 →
      RunV35 h z0 hl cv fh S dst X
        (Y.set c { Y c with base := ⟨(Y c).base.mgr, reseed (Y c).base.tree⟩ }) log

/-! ## The logs the pin's relations keep -/

/-- The obligation an `append` call committed. -/
def CallV35.obligation? : CallV35 → Option Obligation
  | .append c F b => some ⟨F.flowId, b, c⟩
  | _ => none

/-- The `authorizeRefund` call, when the call is one. -/
def CallV35.authCall? : CallV35 → Option AuthCall
  | .authorize a => some a
  | _ => none

/-- The call as the pin's `Contracts.FlowBinding.RunLog` logs it, when it is one. -/
def CallV35.checked? : CallV35 → Option CheckedCall
  | .gate _ e => some (.execute e)
  | .authorize a => some (.authorize a)
  | _ => none

/-- The appended obligations, most recent first: the log `SysSteps` keeps. -/
def appendLog (log : List CallV35) : List Obligation := log.filterMap CallV35.obligation?

/-- The `authorizeRefund` calls, most recent first: the log `ReachLog` keeps. -/
def authLog (log : List CallV35) : List AuthCall := log.filterMap CallV35.authCall?

/-- The calls that check a flow id, most recent first: the log `RunLog` keeps. -/
def checkedLog (log : List CallV35) : List CheckedCall := log.filterMap CallV35.checked?

/-! ## The witness worlds

Chains `0` and `1`, the pin's `mixedSystem 1` as the fixed history (chain `0` committed the value
`1` in batch 0, chain `1` never committed), commit value `1`, and `lengthFlowHash`.  The one-leg
flow `subsetFlow 0 1` (leg `⟨0, 1⟩`) executes on chain `1`; the two-leg flow `mixedFlow 1 1 2`
has its leg `⟨1, 2⟩` appended on chain `1` and refunded there. -/

/-- Bundle `1` goes to chain `1`, every other bundle to chain `0`. -/
def witnessDst : UInt256 → Chain := fun b => if b = 1 then 1 else 0

/-- Every chain allows and registers every peer. -/
def openHub : Hub := ⟨fun _ => true, fun _ => true⟩

/-- No chain allows or registers any peer. -/
def closedHub : Hub := ⟨fun _ => false, fun _ => false⟩

end Contracts.SystemAtV35
