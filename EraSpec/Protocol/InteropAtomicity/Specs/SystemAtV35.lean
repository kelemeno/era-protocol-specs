import EraSpec.Protocol.InteropAtomicity.Specs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg
import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachine

/-!
# Model at `draft/v0.35.0`: every chain's atomic-interop storage, with the v35 entry points

**Commit.** matter-labs/era-contracts, branch `draft/v0.35.0` at `b17415d20`.  Paths are relative
to `l1-contracts/contracts/` unless they start with `protocol-docs/`.  This model was first
written against `d9f678900e`; between that commit and `b17415d20` no file under
`atomic-interop/`, `interop/`, `core/bridgehub/`, `core/chain-registration/`, `common/libraries/`
or `l2-upgrades/` changed, so every line cited below is the same at both commits.  Every other
model in this folder describes the pinned tree `c67894b9`; none of them is changed here.

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
| receive filter in `requireFlowFinalized` / `authorizeRefund` | `L2Bridgehub.isPeerAllowed` | `atomic-interop/AtomicFlowManager.sol:201, :231, :338-344`; `core/bridgehub/L2Bridgehub.sol:43` |
| registration of the other legs' sources in `append` | `L2Bridgehub.baseTokenAssetId` | `AtomicFlowManager.sol:149-160` |
| send-side destination checks | both of the above | `interop/InteropCenter.sol:629-631, :696-704` |
| expired-flow gate in `append` | `L2InteropRootStorage.latestInteropRootTimestamp` | `AtomicFlowManager.sol:112-125`; `interop/L2InteropRootStorage.sol:36, :98-100` |
| imported root after the deadline in `authorizeRefund` | `L2InteropRootStorage.interopRoots` | `atomic-interop/libraries/AtomicInteropProof.sol:94-100` |
| verify, then execute or unbundle, without a second gate | `InteropHandlerBase.bundleStatus` | `interop/interop-handler/L2InteropHandler.sol:61-92`; `interop/interop-handler/InteropHandlerBase.sol:55` |

and the tree's `insert` walks from a stale hint without a hop bound
(`common/libraries/IndexedMerkleTree.sol:90-93`).  `RunV35` below is one relation over all of
it, so that ordering facts between these pieces (an `authorizeRefund` on chain `x` before an
`append` on `x`; a `verifyAtomicBundle` before a deregistration) can be stated at all.

## The state, per chain

* `base` — the pin's `Contracts.AppendPath.ChainState`: the flow manager's `_state`
  (`AtomicFlowManager.sol:61`) and the commitment tree's list state
  (`atomic-interop/L2InteropCommitmentTree.sol:32`; `IndexedMerkleTree.sol:30-34`).
* `hub` — the two `L2Bridgehub` entries per peer chain the atomic path reads: `isPeerAllowed`
  and whether `baseTokenAssetId` is nonzero.
* `roots` — the settlement-layer (L1) half of `L2InteropRootStorage`: the timestamp stored at
  each settlement-layer batch (`0` = nothing imported) and `latestInteropRootTimestamp`.
  Every atomic entry point first requires the flow's settlement layer to be L1
  (`_checkSettlementLayerIsL1`, `AtomicFlowManager.sol:110, :183, :218, :329-333`), and both
  readers above read the entry of that settlement layer, so the other chains' entries are not
  modelled.
* `status` — `InteropHandlerBase.bundleStatus` (`InteropHandlerBase.sol:55`), per bundle hash.

## The steps, and what each one models

* `append` — `InteropCenter._sendBundle` → `_dispatchBundle` → `AtomicFlowManager.append`
  (`InteropCenter.sol:533-613, :727-750`; `AtomicFlowManager.sol:104-173`).  The checks are the
  fields of `AppendOkV35`, together with the send-side destination checks.  The tree insert is
  `InsertOkV35`: the pin's `InsertSucceeds` with the hop bound removed.  The logged call
  carries the bundle's destination chain, the `_destinationChainId` the send-side checks read.
* `importRoot` — `L2InteropRootStorage._addInteropRoot` for the L1 entry
  (`L2InteropRootStorage.sol:70-103`), called only by the bootloader (`:20-25, :50-68`).
* `gate` — `verifyAtomicBundle` (`L2InteropHandler.sol:83-92`, to `Verified`) or
  `executeAtomicBundle` on an `Unreceived` bundle (`:61-78`, to `FullyExecuted`).  Both run
  `requireFlowFinalized` (`AtomicFlowManager.sol:176-213`), here `GateOkV35`.
* `resume` — the two status edges that run NO gate: `executeAtomicBundle` on a `Verified`
  bundle (`L2InteropHandler.sol:73-77`) and `unbundleBundle` (`InteropHandlerBase.sol:113-175`).
* `authorize` — `authorizeRefund` (`AtomicFlowManager.sol:216-247`), one marked leg per step,
  on the leg's declared chain, as in the pin's `ReachLog` (see "What differs from the code").
* `claim` — `claimRefund` (`AtomicFlowManager.sol:250-265`).
* `admin` — the writers of the two bridgehub entries: `L2Bridgehub.allowInteropPeer`
  (`L2Bridgehub.sol:95-99`), `deregisterChainForInterop` (`:102-105`), and
  `BridgehubBase.forwardedBridgeMint` (`core/bridgehub/BridgehubBase.sol:432-453`), which writes
  `baseTokenAssetId` (`:447`) and leaves `isPeerAllowed` alone.  No other function of
  `L2Bridgehub` or `BridgehubBase` writes either entry.  Every admin step is enabled for every
  pair at every moment.
* `initL2` — `L2InteropCommitmentTree.initL2` (`L2InteropCommitmentTree.sol:45-48`).  At v35
  only the genesis upgrade calls it (`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:230-232,
  :373`); the step is kept, with the pin's `leafCount = 0` guard, as an over-approximation.

The log records every `append`, every gate call, every `authorizeRefund` step and every admin
step, most recent first.  `importRoot`, `resume`, `claim` and `initL2` are not logged.

## What differs from the code

Each item below either removes a check (so the model admits more runs than the code) or is
stated with the result that bounds it.

* `authorizeRefund` marks, in one call, every `Committed` key of the presented flow in the
  manager of the chain that RUNS it (`AtomicFlowManager.sol:236-246`), whatever chain the flow
  declares for that leg, and reads that chain's root storage and bridgehub.  Like the pin's
  `ReachLog`, `authorize` marks one leg per step, on the leg's declared chain, and reads that
  chain's state; one code call that marks several keys is represented by several consecutive
  `authorize` steps with the same flow and evidence, each logged.  So "the chain that runs the
  call" is `a.leg.chain` here.  At v35 `append` requires the committing leg to be declared on
  the committing chain (`:141-147`), and on runs from genesis
  `Contracts.SystemAtV35.Properties.CodeAuthorizeMarksDeclaredLegOrLoggedClashV35` shows that a
  `Committed` key the code would mark is declared by the presented flow on the marking chain,
  or the presented flow clashes on `fh` with the flow of a logged `append`.
* The flow canonicalization (`_validateAndComputeFlowId`, `:360-379`: version, leg cap,
  strictly ascending bundle hashes) runs on all three paths.  The model keeps the leg cap and
  the ordering on `append` only, and folds the `version` byte and the settlement-layer field
  (`atomic-interop/IAtomicInterop.sol:50-56`) into `FlowHash`, as at the pin.
* Nothing ties a bundle hash to its destination: the gate may run on any chain for any
  bundle hash.  In the code the hash commits to the bundle's `destinationChainId`
  (`InteropCenter.sol:690-692`) and the handler checks it (`InteropHandlerBase.sol:400-403`).
* The handler's execution-address, unbundler-address and destination base-token checks, the
  per-call statuses (`InteropHandlerBase.sol:113-175, :239-300, :390-410`), the bundle salt
  check and the atomic-to-L1 check of the center (`InteropCenter.sol:552-566`), the tree's leaf
  report hook (`L2InteropCommitmentTree.sol:62, :71-91`), the other root-storage checks
  (`L2InteropRootStorage.sol:77-82`), and who may send admin steps
  (`core/chain-registration/ChainRegistrationSender.sol:77-153`; `onlyChainRegistrationSender`,
  `L2Bridgehub.sol:45-53`): they only reject.
* The import guard `InteropRootAlreadyExists` is keyed on the stored root (`:89-91`); the model
  keys it on the stored timestamp.  Every import writes a nonzero root and a nonzero timestamp
  together (`:80-87, :93`), so the two agree on every state reachable from empty storage.
* The tree side of every proof is the fixed history `S`, exactly as at the pin.  The imported
  roots in `roots` carry only their timestamps; which root a proof authenticates against stays
  inside `S`, and `authorize` asks only that SOME imported L1 root post-dates the deadline.
* Registrations made before v35 by the removed `registerChain` set `baseTokenAssetId` and never
  `isPeerAllowed` (`protocol-docs/interop-gating.md:175-177, :207-215`).  They are part of the
  starting bridgehub, not steps.
-/

namespace Contracts.SystemAtV35

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.FlowBinding Contracts.AppendPath

/-- `InteropHandlerBase.bundleStatus`'s type `BundleStatus` (`common/Messaging.sol`), as
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

which has no hop bound at v35 (the NatSpec at `:59-62` calls it "deliberately unbounded").  The
insert succeeds only if the walk exits, here at `low` after some finite number of hops.  The
pin's `Contracts.AppendPath.InsertSucceeds` is the same structure with the walk cut at
`MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5` hops (`lowSearch … maxLowIndexSearchAttempts`).  The writes (`:95-106`) are the pin's
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
  /-- `IMTLowLeafValueTooLarge` (`:86-88`). -/
  hintBelow : (T.leaf hint).value < v
  /-- The unbounded walk (`:90-93`) exits at `low`. -/
  walk : ∃ hops : ℕ, lowSearch T v hops hint = some low

/-! ## The other contracts' state the atomic path reads -/

/-- One chain's `L2Bridgehub` entries for every peer chain `s`: `peer s` is
`isPeerAllowed[s]` (`core/bridgehub/L2Bridgehub.sol:43`), and `registered s` is
`baseTokenAssetId[s] != bytes32(0)` (`core/bridgehub/BridgehubBase.sol:96`). -/
structure Hub where
  peer : Chain → Bool
  registered : Chain → Bool

/-- **`_checkLegSourceAllowed(s)` PASSES ON CHAIN `c`** (`AtomicFlowManager.sol:338-344`): `s` is
`block.chainid`, or `c`'s bridgehub allows `s`.  This is the receive filter of
`protocol-docs/interop-gating.md:185-203`. -/
def SourceAllowed (H : Hub) (c s : Chain) : Prop := s = c ∨ H.peer s = true

instance (H : Hub) (c s : Chain) : Decidable (SourceAllowed H c s) := by
  unfold SourceAllowed; infer_instance

/-- An admin step on one chain's bridgehub. -/
inductive AdminOp where
  /-- `L2Bridgehub.allowInteropPeer(s, assetId)` (`L2Bridgehub.sol:95-99`): requires a nonzero
  `assetId` (`:96`), writes it to `baseTokenAssetId[s]` (`:97`) and sets `isPeerAllowed[s]`
  (`:98`). -/
  | allow (s : Chain)
  /-- `L2Bridgehub.deregisterChainForInterop(s)` (`L2Bridgehub.sol:102-105`): deletes both. -/
  | deregister (s : Chain)
  /-- `BridgehubBase.forwardedBridgeMint` for chain `s` (`core/bridgehub/BridgehubBase.sol:432-453`):
  writes `baseTokenAssetId[s]` (`:447`) and leaves `isPeerAllowed[s]` alone.  `r` says whether
  the written asset id is nonzero; both values are allowed. -/
  | setBaseToken (s : Chain) (r : Bool)

/-- The bridgehub after the admin step. -/
def AdminOp.apply : AdminOp → Hub → Hub
  | .allow s, H => ⟨fun x => if x = s then true else H.peer x,
      fun x => if x = s then true else H.registered x⟩
  | .deregister s, H => ⟨fun x => if x = s then false else H.peer x,
      fun x => if x = s then false else H.registered x⟩
  | .setBaseToken s r, H => ⟨H.peer, fun x => if x = s then r else H.registered x⟩

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

/-- Every chain's bridgehub. -/
def WorldV35.hubs (W : WorldV35) : Chain → Hub := fun c => (W c).hub

/-- One bundle's status updated. -/
def setStatus (st : UInt256 → BundleStatus) (b : UInt256) (s : BundleStatus) :
    UInt256 → BundleStatus :=
  fun b' => if b' = b then s else st b'

/-- **GENESIS AT v35.**  Every chain after the genesis upgrade: the pin's `genesis` (empty manager,
`setup` tree), nothing imported, every bundle `Unreceived`, and the bridgehub in any state `H0 c`
(entries written before the atomic path runs, legacy registrations included). -/
def genesisV35 (H0 : Chain → Hub) : WorldV35 :=
  fun c => ⟨genesis, H0 c, ⟨fun _ => 0, 0⟩, fun _ => .Unreceived⟩

/-- **THE ROOT STORAGE KEEPS ITS RUNNING MAXIMUM.**  On every chain, every stored L1 timestamp
is at most `latestInteropRootTimestamp[L1]`.  `_addInteropRoot` is the only writer of either
mapping and keeps the maximum (`L2InteropRootStorage.sol:93, :98-100`).  It holds at
`genesisV35`, and every step keeps it
(`Contracts.SystemAtV35.Properties.LatestRootTimestampMonotoneMaxV35`). -/
def RootsWf (W : WorldV35) : Prop := ∀ c blk, (W c).roots.stored blk ≤ (W c).roots.latest

/-! ## The entry points' checks -/

/-- `MAX_ATOMIC_FLOW_LEGS` (`atomic-interop/IAtomicInterop.sol:99`). -/
def maxAtomicFlowLegs : ℕ := 8

/-- **`append(b, hint, F)` SUCCEEDS ON CHAIN `c` AT v35, THE TREE LANDING ON `low`**, as reached
from `InteropCenter._sendBundle` (`interop/InteropCenter.sol:533-613`) for a bundle to chain
`dest`.  The fields are the checks in call order. -/
structure AppendOkV35 (cv : CommitValue) (fh : FlowHash) (x : ChainV35) (c : Chain) (F : Flow)
    (b : UInt256) (dest : Chain) (hint low : ℕ) : Prop where
  /-- `DestinationChainNotRegistered` (`InteropCenter.sol:697-698`, via `_buildInteropBundle`
  `:629-631`). -/
  destRegistered : x.hub.registered dest = true
  /-- `DestinationChainNotAllowed` (`InteropCenter.sol:699-702`): the send-side allowlist. -/
  destAllowed : x.hub.peer dest = true
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
  (`:130-147`).  With `sorted`, the first index carrying `b` is the only one, so "it declares
  this chain" is membership of `⟨c, b⟩`. -/
  isLegHere : (⟨c, b⟩ : FlowLeg) ∈ F.legs
  /-- `ManagerLegSourceChainNotRegistered` (`:149-160`). -/
  othersRegistered : ∀ l ∈ F.legs, l.chain ≠ c → x.hub.registered l.chain = true
  /-- `ManagerLegAlreadyCommitted` (`:162-164`). -/
  legUnset : AppendGuard x.base.mgr F.flowId b
  /-- The tree's `insert(commitValue(flowId, b), hint)` (`:168-170`;
  `L2InteropCommitmentTree.sol:51-64`). -/
  treeInsert : InsertOkV35 x.base.tree (cv F.flowId b) hint low

/-- **COUNTERFACTUAL: `append` WITHOUT THE EXPIRED-FLOW GATE.**  `AppendOkV35` minus `notExpired`
(`ManagerFlowDeadlinePassed`, `AtomicFlowManager.sol:120-125`).  This is not the v35 contract;
the pin's `append` had no such gate.  It is used only to show, on one run, that this one check
is what stops a new leg of a refunded flow from being committed on the chain that refunded it
(`Contracts.SystemAtV35.Properties.WithoutDeadlineGateAppendAfterRefundV35`). -/
structure AppendOkV35WithoutDeadlineGate (cv : CommitValue) (fh : FlowHash) (x : ChainV35)
    (c : Chain) (F : Flow) (b : UInt256) (dest : Chain) (hint low : ℕ) : Prop where
  destRegistered : x.hub.registered dest = true
  destAllowed : x.hub.peer dest = true
  flowId : FlowIdChecked fh F
  legCap : F.legs.length ≤ maxAtomicFlowLegs
  sorted : (F.legs.map FlowLeg.bundleHash).Pairwise (· < ·)
  isLegHere : (⟨c, b⟩ : FlowLeg) ∈ F.legs
  othersRegistered : ∀ l ∈ F.legs, l.chain ≠ c → x.hub.registered l.chain = true
  legUnset : AppendGuard x.base.mgr F.flowId b
  treeInsert : InsertOkV35 x.base.tree (cv F.flowId b) hint low

/-- **`requireFlowFinalized` PASSES ON CHAIN `d` AT v35** (`AtomicFlowManager.sol:176-213`) for
the logged call `e`: the pin's checks on the call's own evidence (`ExecCall.Verified`:
`_checkFlowId` `:182`, the inclusion proof of every leg `:194-209`, membership of the executing
bundle `:210-212`), and the receive filter on every leg's source (`:201`), read on `x`, the state
of chain `d`. -/
def GateOkV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (x : ChainV35) (d : Chain) (e : ExecCall) : Prop :=
  e.Verified h z0 hl cv fh S ∧ ∀ l ∈ e.flow.legs, SourceAllowed x.hub d l.chain

/-- **`authorizeRefund` PASSES AT v35** (`AtomicFlowManager.sol:216-247`) for the logged call `a`,
read on `x`, the state of chain `a.leg.chain`: the pin's checks (`AuthCall.Verified`:
`_checkFlowId` `:217`, the missing leg in the flow `:224-226`, the proof bound to its declared
chain `:227-230`, the absence proof of `verifyTimeoutAbsence` `:233-234`), the receive filter on
the missing leg's source (`:231`), and an imported L1 root whose timestamp is after the deadline
(`atomic-interop/libraries/AtomicInteropProof.sol:94-100`:
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
  /-- `unbundleBundle` on a `Verified` bundle (`InteropHandlerBase.sol:139, :147`). -/
  | unbundleFirst : NoGateEdge .Verified .Unbundled
  /-- `unbundleBundle` again (`:139, :147`). -/
  | unbundleAgain : NoGateEdge .Unbundled .Unbundled

/-! ## The calls and the run -/

/-- One logged call of a v35 run. -/
inductive CallV35 where
  /-- `append(b, _, F)` succeeded on chain `c`, sending bundle `b` to chain `dest`. -/
  | append (c : Chain) (F : Flow) (b : UInt256) (dest : Chain)
  /-- `requireFlowFinalized` passed on chain `d` for `e` (from `verifyAtomicBundle`, or from
  `executeAtomicBundle` on an `Unreceived` bundle). -/
  | gate (d : Chain) (e : ExecCall)
  /-- One leg of `authorizeRefund` for `a`, on chain `a.leg.chain`. -/
  | authorize (a : AuthCall)
  /-- An admin step on chain `c`'s bridgehub. -/
  | admin (c : Chain) (op : AdminOp)

/-- **EVERY INTERLEAVING OF EVERY CHAIN'S ATOMIC-INTEROP CALLS AT v35, LOGGED.**
`RunV35 h z0 hl cv fh S X Y log`: from `X` the chains reach `Y`; `log` lists the logged calls,
most recent first. -/
inductive RunV35 (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (X : WorldV35) : WorldV35 → List CallV35 → Prop
  | refl : RunV35 h z0 hl cv fh S X X []
  /-- `InteropCenter._sendBundle` → `AtomicFlowManager.append` on chain `c`: the leg is
  `Committed` and its commit value inserted (`ChainState.appended`). -/
  | append {Y log c F b dest hint low} : RunV35 h z0 hl cv fh S X Y log →
      AppendOkV35 cv fh (Y c) c F b dest hint low →
      RunV35 h z0 hl cv fh S X
        (Y.set c { Y c with base := (Y c).base.appended cv F.flowId b low })
        (.append c F b dest :: log)
  /-- `L2InteropRootStorage._addInteropRoot(L1, blk, t, _)` on chain `c`
  (`InteropRootTimestampIsZero` `:85-87`; `InteropRootAlreadyExists` `:89-91`, read here as
  "nothing imported at `blk`"). -/
  | importRoot {Y log c blk t} : RunV35 h z0 hl cv fh S X Y log → 0 < t →
      (Y c).roots.stored blk = 0 →
      RunV35 h z0 hl cv fh S X (Y.set c { Y c with roots := (Y c).roots.import blk t }) log
  /-- `verifyAtomicBundle` (to `Verified`) or `executeAtomicBundle` on an `Unreceived` bundle (to
  `FullyExecuted`) on chain `d`: the status check (`InteropHandlerBase.sol:313`, `:282-287`)
  and the gate. -/
  | gate {Y log d e st} : RunV35 h z0 hl cv fh S X Y log →
      (Y d).status e.leg.bundleHash = .Unreceived →
      (st = .Verified ∨ st = .FullyExecuted) → GateOkV35 h z0 hl cv fh S (Y d) d e →
      RunV35 h z0 hl cv fh S X
        (Y.set d { Y d with status := setStatus (Y d).status e.leg.bundleHash st })
        (.gate d e :: log)
  /-- A status edge that runs no gate, on chain `d`. -/
  | resume {Y log d b st'} : RunV35 h z0 hl cv fh S X Y log →
      NoGateEdge ((Y d).status b) st' →
      RunV35 h z0 hl cv fh S X (Y.set d { Y d with status := setStatus (Y d).status b st' }) log
  /-- `authorizeRefund`, marking the leg `a.leg` of the checked flow `a.flow` on its chain. -/
  | authorize {Y log} (a : AuthCall) : RunV35 h z0 hl cv fh S X Y log →
      AuthorizeOkV35 h z0 hl cv fh S (Y a.leg.chain) a →
      AuthorizeGuard (Y a.leg.chain).base.mgr a.flow.flowId a.leg.bundleHash →
      RunV35 h z0 hl cv fh S X
        (Y.set a.leg.chain { Y a.leg.chain with
          base := ⟨(Y a.leg.chain).base.mgr.set a.flow.flowId a.leg.bundleHash .Revertable,
            (Y a.leg.chain).base.tree⟩ })
        (.authorize a :: log)
  /-- `claimRefund` on chain `c`. -/
  | claim {Y log c f b} : RunV35 h z0 hl cv fh S X Y log →
      ClaimGuard (Y c).base.mgr f b →
      RunV35 h z0 hl cv fh S X
        (Y.set c { Y c with base := ⟨(Y c).base.mgr.set f b .Reverted, (Y c).base.tree⟩ }) log
  /-- An admin step on chain `c`'s bridgehub. -/
  | admin {Y log} (c : Chain) (op : AdminOp) : RunV35 h z0 hl cv fh S X Y log →
      RunV35 h z0 hl cv fh S X (Y.set c { Y c with hub := op.apply (Y c).hub })
        (.admin c op :: log)
  /-- `L2InteropCommitmentTree.initL2` on chain `c`. -/
  | initL2 {Y log c} : RunV35 h z0 hl cv fh S X Y log →
      (Y c).base.tree.leafCount = 0 →
      RunV35 h z0 hl cv fh S X
        (Y.set c { Y c with base := ⟨(Y c).base.mgr, reseed (Y c).base.tree⟩ }) log

/-! ## The logs the pin's relations keep -/

/-- The `authorizeRefund` call, when the call is one. -/
def CallV35.authCall? : CallV35 → Option AuthCall
  | .authorize a => some a
  | _ => none

/-- The call as the pin's `Contracts.FlowBinding.RunLog` logs it, when it is one. -/
def CallV35.checked? : CallV35 → Option CheckedCall
  | .gate _ e => some (.execute e)
  | .authorize a => some (.authorize a)
  | _ => none

/-- The obligation an `append` call committed: the flow id, the bundle and the committing chain,
as in the pin's `Contracts.AppendPath.Steps` log. -/
def CallV35.obligation? : CallV35 → Option Obligation
  | .append c F b _ => some ⟨F.flowId, b, c⟩
  | _ => none

/-- The appended obligations, most recent first. -/
def appendLog (log : List CallV35) : List Obligation := log.filterMap CallV35.obligation?

/-- The `authorizeRefund` calls, most recent first: the log `ReachLog` keeps. -/
def authLog (log : List CallV35) : List AuthCall := log.filterMap CallV35.authCall?

/-- The calls that check a flow id, most recent first: the log `RunLog` keeps. -/
def checkedLog (log : List CallV35) : List CheckedCall := log.filterMap CallV35.checked?

/-! ## The bridgehubs, replayed from the log

Only `admin` steps write a bridgehub, and every `admin` step is logged.  So the bridgehubs at
any point of a run are the starting ones with the admin calls logged up to that point
replayed in order. -/

/-- **THE BRIDGEHUBS AFTER THE ADMIN CALLS OF `log`.**  The admin calls of `log` (most recent
first) replayed, oldest first, on the bridgehubs `H`. -/
def hubsAfter (H : Chain → Hub) : List CallV35 → Chain → Hub
  | [] => H
  | .admin c op :: log => fun x => if x = c then op.apply (hubsAfter H log c) else hubsAfter H log x
  | .append _ _ _ _ :: log => hubsAfter H log
  | .gate _ _ :: log => hubsAfter H log
  | .authorize _ :: log => hubsAfter H log

/-! ## Witness objects

Chains `0`, `1` and `2`, the pin's `mixedSystem 1` as the fixed history (chain `0` committed the
value `1` in batch 0; chains `1` and `2` never committed; batch `n` settled at time `n`), the
commit value `v35BundleCv` (a leg's commit value is its bundle hash) and `lengthFlowHash` (a
one-leg flow has id `0`, every other flow id `1`). -/

/-- The commit value of every leg is its bundle hash. -/
def v35BundleCv : CommitValue := fun _ b => b

/-- No chain allows or registers any peer. -/
def v35ClosedHub : Hub := ⟨fun _ => false, fun _ => false⟩

/-- A three-leg flow with deadline `0`: leg `⟨0, 1⟩` on chain `0`, legs `⟨1, 2⟩` and `⟨1, 3⟩` on
chain `1`.  `lengthFlowHash` checks it with id `1`. -/
def v35RefundFlow : Flow := ⟨1, [⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 3⟩], 0⟩

/-- A one-leg flow on chain `1` with the later deadline `1`.  `lengthFlowHash` checks it with
id `0`. -/
def v35LaterFlow : Flow := ⟨0, [⟨1, 4⟩], 1⟩

/-- A two-leg flow with deadline `0`: leg `⟨0, 2⟩` on chain `0`, leg `⟨2, 3⟩` on chain `2`.
`lengthFlowHash` checks it with id `1`. -/
def v35PeerRefundFlow : Flow := ⟨1, [⟨0, 2⟩, ⟨2, 3⟩], 0⟩

/-- A two-leg flow with id `1` that declares bundle `1` on chain `1`.  `lengthFlowHash` checks
it with id `1`, so its preimage clashes with `v35RefundFlow`'s, which declares bundle `1` on
chain `0`. -/
def v35ClashFlow : Flow := ⟨1, [⟨1, 1⟩, ⟨1, 7⟩], 0⟩

end Contracts.SystemAtV35
