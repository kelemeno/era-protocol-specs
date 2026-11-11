import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg
import EraSpec.Protocol.InteropAtomicity.Specs.FlowBinding
import EraSpec.Contracts.AtomicFlowManager.Specs.FlowCanonicalAtHead

/-!
# Model: `append` binds the leg to its flow preimage, at head (`3605e82`)

Source: matter-labs/era-contracts `main` at commit `3605e82` (2026-11), commits #2312 and
#2339. Paths are relative to `l1-contracts/contracts/` at that commit. The pin models
(`Specs/Refund.lean`, `Specs/FlowBinding.lean`, `Specs/OncePerLeg.lean`, all `c67894b9`)
are not changed; this file models the head code next to them and reuses their state,
evidence and gate definitions.

**This file is definitions only.** Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.FlowBindingAtHead`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.FlowBindingAtHead`.

## The code at `3605e82`

`InteropCenter._dispatchBundle` (`interop/InteropCenter.sol:721-741`) hashes the bundle
(`:725`, `keccak256(abi.encode(bundle))`, the bundle carrying `sourceChainId: block.chainid`,
`:633`) and, for an L2 destination, calls the manager with the sender's out-of-band
preimage (`:736-740`). `append` (`atomic-interop/AtomicFlowManager.sol:103-172`) then runs,
in this order:

    bytes32 flowId = _validateAndComputeFlowId(_flowPreimage);                          // :108
    _checkSettlementLayerIsL1(_flowPreimage.settlementLayerChainId);                    // :109
    if (L2_INTEROP_ROOT_STORAGE.latestInteropRootTimestamp(sl) > _flowPreimage.deadline)
        revert ManagerFlowDeadlinePassed(..);                                           // :119-124
    // first i with legBundleHashes[i] == _bundleHash, else ManagerCommittedBundleNotInFlow  :129-139
    if (_flowPreimage.legSourceChainIds[legIndex] != block.chainid)
        revert ManagerCommittedLegSourceChainMismatch(..);                              // :140-146
    // every leg source other than block.chainid has L2_BRIDGEHUB.baseTokenAssetId != 0      :151-159
    if (_state[flowId][_bundleHash] != LegState.Unset) revert ManagerLegAlreadyCommitted(..); // :161-163
    _state[flowId][_bundleHash] = LegState.Committed;                                   // :165
    uint256 value = AtomicInteropProof.commitValue(flowId, _bundleHash);                // :167
    (uint256 index, ) = IL2InteropCommitmentTree(commitmentTree()).insert(value, _lowNullifierIndex); // :169

The tree's insert is `IndexedMerkleTree.insert` (`common/libraries/IndexedMerkleTree.sol:65-107`),
with the same checks as at the pin except that the low-leaf walk is now unbounded
(`:90-93`, `while (lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value)`).

`requireFlowFinalized` (`atomic-interop/AtomicFlowManager.sol:175-211`) runs `_checkFlowId`
(`:181`), the settlement-layer check (`:182`), the proof count (`:184-187`), and per leg the
proof's source chain (`:197-199`) and `verifyInclusion` (`:200-206`); the executing bundle
must be a leg (`:193-196, :208-210`). It is reached from `L2InteropHandler.executeAtomicBundle`
(`interop/interop-handler/L2InteropHandler.sol:63-65`) and `verifyAtomicBundle` (`:79`).

`authorizeRefund` (`AtomicFlowManager.sol:214-244`) runs `_checkFlowId` (`:215`), the
settlement-layer check (`:216`), the missing-leg index bound (`:222-224`), the proof's source
chain against the missing leg's declared one (`:225-228`) and `verifyTimeoutAbsence`
(`:230-231`). Then it marks **this chain's** `Committed` legs of the presented flow
`Revertable` (`:235-243`): it reads and writes `_state[_flow.flowId][legBundleHashes[i]]` of
the manager that runs the call, whatever chain the flow declares for that leg.

`claimRefund(_flowId, _bundle)` (`:247-262`) is unchanged in shape: a raw key, guarded only
by `Revertable`.

## What changed from the pin

At `c67894b9`, `append(_flowId, _bundleHash, _deadline, _lowNullifierIndex)`
(`AtomicFlowManager.sol:87-102`) ran only the `Unset` guard and the insert. The flow a leg
was committed under was never recorded on chain, and nothing tied the leg's declared source
chain to the chain that committed it. `Contracts.FlowBinding` (`Specs/FlowBinding.lean`)
says so: only flows presented to `requireFlowFinalized` and `authorizeRefund` were ever seen.
At head every one of the three entry points takes a preimage and runs
`_validateAndComputeFlowId` (`Contracts.FlowCanonicalAtHead`), so the run below logs a
preimage for every call, `append` included.

## What is modelled

`RunAtHead` interleaves, over every chain at once, the head `append` (manager and tree in one
step, as in `Contracts.AppendPath.SysSteps`), `requireFlowFinalized`, `authorizeRefund`,
`claimRefund` and the tree's `initL2`. Its log holds every call that takes a preimage, most
recent first.

* `append` is `AppendSucceedsAtHead`: every check above, in source order, and both writes.
  The values it reads from other contracts (`latestInteropRootTimestamp`, the Bridgehub's
  `baseTokenAssetId`) are the call's `AppendEnv`, arbitrary at each call and logged with it.
* `authorizeRefund` marks one leg per step, as in the pin models. Unlike the pin's
  `Contracts.Refund.ReachLog`, which marks the leg in the manager of the leg's DECLARED chain,
  the step here marks it in the manager of the chain that RUNS the call (`AuthCallAtHead.chain`),
  as the code does (`:235-243`). Whether those coincide is a result
  (`Contracts.FlowBindingAtHead.Properties.AuthorizeMarksDeclaredLegOrLoggedClash`), not an
  assumption.
* `requireFlowFinalized` and `authorizeRefund` check their evidence against the fixed history
  `S` (`Contracts.Atomicity.System`), exactly as in `Contracts.Refund`. `S` is not tied to the
  live trees; that is the operational projection (A5).
* The flow id is `enc preimage` (`Contracts.FlowCanonicalAtHead.PreimageHash`), the commit
  value `cv flowId bundleHash`; no property of either is assumed.

Omitted checks, all reject-only (so every safety result holds a fortiori): the callers
(`onlyInteropCenter` `:87-92, :107`, `onlyInteropHandler` `:95-100, :178`), the proof count
(`:184-187`), the root-authentication and settlement-layer metadata checks inside
`verifyInclusion`/`verifyTimeoutAbsence` (`atomic-interop/libraries/AtomicInteropProof.sol:44-124`)
beyond what `LegFinalizedBy`/`LegRefundableBy` keep, the imported-root timestamp check of
`verifyTimeoutAbsence` (`:94-100`), the handler's pause, permission, destination and
`bundleStatus` checks (`L2InteropHandler.sol:51-68`), and the commitment tree's L2→L1 leaf
report after insert (`atomic-interop/L2InteropCommitmentTree.sol:50-63`). Also not modelled:
`claimRefund`'s recovery calls (`AtomicFlowManager.sol:289-322`, item H-2), events, and
upgrades of either contract (`OPS-CONFIG`). Callers are fixed by the step set.
-/

namespace Contracts.FlowBindingAtHead

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath
open Contracts.FlowCanonicalAtHead

/-! ## The pin's view of a head flow -/

/-- The pin model's leg list of a head preimage: leg `i` is
`⟨legSourceChainIds[i], legBundleHashes[i]⟩`. -/
def pinLegs (P : FlowPreimage) : List FlowLeg :=
  P.legPairs.map (fun p => ⟨p.2, p.1⟩)

/-- The pin model's `Contracts.Atomicity.Flow` for a head `AtomicFlow`: the claimed id, the
legs, the deadline. The version and settlement layer are dropped, as the pin model drops the
settlement layer; every path checks both (`Contracts.FlowCanonicalAtHead.PreimageAccepted`,
`_checkSettlementLayerIsL1`). -/
def pinFlow (F : AtomicFlow) : Flow :=
  ⟨F.flowId, pinLegs F.preimage, F.preimage.deadline⟩

/-- The flow a preimage commits a leg under: the id `append` computes, and the preimage. -/
def committedFlow (enc : PreimageHash) (P : FlowPreimage) : AtomicFlow := ⟨enc P, P⟩

/-- The pin `FlowHash` a head preimage hash induces when the L1 chain id is `l1`: rebuild
the head preimage from the pin's `(legs, deadline)` with version `0x01` and settlement layer
`l1`. A head flow that passes `_checkFlowId` and settles on `l1` passes the pin's
`FlowIdChecked` for this hash
(`Contracts.FlowBindingAtHead.Properties.HeadCheckIsPinCheck`). -/
def pinFlowHash (enc : PreimageHash) (l1 : UInt256) : FlowHash :=
  fun legs d => enc ⟨ATOMIC_FLOW_PREIMAGE_VERSION, d, l1, legs.map FlowLeg.bundleHash,
    legs.map FlowLeg.chain⟩

/-! ## The head `append` -/

/-- **`IndexedMerkleTree.insert(v, hint)` SUCCEEDS AT HEAD, LANDING ON LOW LEAF `low`**
(`common/libraries/IndexedMerkleTree.sol:65-107`). The checks are the pin's
(`Contracts.AppendPath.InsertSucceeds`) except the walk: at head it is unbounded
(`:90-93`), so it exits at `low` after some number of hops. The writes (`:95-106`) are
`Contracts.InteropCommitmentTree.insert T v low`, as at the pin. -/
structure InsertSucceedsAtHead (T : Tree) (v : UInt256) (hint low : ℕ) : Prop where
  /-- `IMTNotInitialized` (`:70-73`). -/
  initialized : Initialized T
  /-- `IMTValueZero` (`:74-76`). -/
  nonzero : v ≠ 0
  /-- `IMTValueAlreadyExists` (`:77-79`): the dedup gate. -/
  fresh : T.valueToIndex v = 0
  /-- `IMTLowLeafIndexOutOfBounds` (`:80-82`). -/
  hintInBounds : hint < T.leafCount
  /-- `IMTLowLeafValueTooLarge` (`:84-88`). -/
  hintBelow : (T.leaf hint).value < v
  /-- The unbounded walk (`:90-93`) exits at `low`. -/
  search : ∃ hops, lowSearch T v hops hint = some low

/-- What `append` reads from contracts outside the manager and the tree, at the moment of the
call. -/
structure AppendEnv where
  /-- `L2_INTEROP_ROOT_STORAGE.latestInteropRootTimestamp(chainId)` (`AtomicFlowManager.sol:119-121`). -/
  latestRootTimestamp : UInt256 → ℕ
  /-- `L2_BRIDGEHUB.baseTokenAssetId(chainId) != bytes32(0)` (`:156`). -/
  registered : UInt256 → Prop

/-- **`append(b, hint, P)` SUCCEEDS ON CHAIN `c`, LANDING ON LOW LEAF `low`**
(`AtomicFlowManager.sol:103-172`). The fields are the checks in source order. The flow id is
`enc P`, the value `_validateAndComputeFlowId` returns. -/
structure AppendSucceedsAtHead (enc : PreimageHash) (cv : CommitValue) (l1 : UInt256)
    (env : AppendEnv) (c : Chain) (s : ChainState) (b : UInt256) (P : FlowPreimage)
    (hint low : ℕ) : Prop where
  /-- `_validateAndComputeFlowId` (`:108`): version, leg cap, sort, lengths. -/
  flowId : validateAndComputeFlowId enc P = some (enc P)
  /-- `_checkSettlementLayerIsL1` (`:109`, `:326-330`). -/
  slIsL1 : P.settlementLayerChainId = l1
  /-- `ManagerFlowDeadlinePassed` (`:119-124`): the expired-flow gate. -/
  notExpired : env.latestRootTimestamp P.settlementLayerChainId ≤ P.deadline
  /-- `ManagerCommittedBundleNotInFlow` and `ManagerCommittedLegSourceChainMismatch`
  (`:129-146`): the first index carrying `b` declares this chain. -/
  isLegHere : ∃ i, P.legBundleHashes.idxOf? b = some i ∧ P.legSourceChainIds[i]? = some c
  /-- `ManagerLegSourceChainNotRegistered` (`:151-159`). -/
  othersRegistered : ∀ src ∈ P.legSourceChainIds, src ≠ c → env.registered src
  /-- `ManagerLegAlreadyCommitted` (`:161-163`). -/
  legUnset : AppendGuard s.mgr (enc P) b
  /-- The tree's `insert(commitValue(flowId, b), hint)` (`:167-169`). -/
  treeInsert : InsertSucceedsAtHead s.tree (cv (enc P) b) hint low

/-! ## The calls, logged -/

/-- One successful `append` call, as it happened. -/
structure AppendCall where
  /-- The chain that ran it (`block.chainid`). -/
  chain : Chain
  /-- `_bundleHash`. -/
  bundleHash : UInt256
  /-- `_flowPreimage`. -/
  preimage : FlowPreimage
  /-- What the call read from outside the manager and the tree. -/
  env : AppendEnv

/-- The obligation an `append` commits: the computed id, the bundle hash, the chain that ran
it. -/
def AppendCall.obligation (enc : PreimageHash) (a : AppendCall) : Obligation :=
  ⟨enc a.preimage, a.bundleHash, a.chain⟩

/-- One successful `requireFlowFinalized(_executingBundleHash, _finality)` call. -/
structure ExecCallAtHead where
  /-- `_finality.flow`. -/
  flow : AtomicFlow
  /-- The batch and IMT inclusion proof submitted for each leg (`_finality.proofs`). -/
  evidence : GateEvidence
  /-- `_executingBundleHash`. -/
  executing : UInt256

/-- The checks `requireFlowFinalized` runs (`AtomicFlowManager.sol:175-211`): `_checkFlowId`,
the settlement layer, the executing bundle is a leg, and every leg's inclusion proof verifies
against an on-time batch of its declared source chain. -/
def ExecCallAtHead.Verified (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (enc : PreimageHash) (l1 : UInt256) (S : System) (e : ExecCallAtHead) : Prop :=
  CheckFlowId enc e.flow ∧ e.flow.preimage.settlementLayerChainId = l1
    ∧ e.executing ∈ e.flow.preimage.legBundleHashes
    ∧ FlowFinalizedBy h z0 hl cv S (pinFlow e.flow) e.evidence

/-- One `authorizeRefund(_flow, _missingLegIndex, _absence)` call, taken one marked leg at a
time. -/
structure AuthCallAtHead where
  /-- The chain whose manager runs the call (`block.chainid`). -/
  chain : Chain
  /-- `_flow`. -/
  flow : AtomicFlow
  /-- The bundle hash `legBundleHashes[i]` this step marks `Revertable` on `chain`. -/
  marked : UInt256
  /-- The leg at `_missingLegIndex`, whose absence the proof shows. -/
  missing : FlowLeg
  /-- The batch the absence proof is against. -/
  batch : ℕ
  /-- The IMT absence proof (`_absence`). -/
  proof : ImtProof

/-- The checks `authorizeRefund` runs (`AtomicFlowManager.sol:214-231`), on the call's own
evidence, and the loop's leg (`:235-237`). `LegRefundableBy` is against the missing leg's
declared chain, which is the `ProofSourceChainMismatch` check (`:225-228`). -/
def AuthCallAtHead.Verified (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (enc : PreimageHash) (l1 : UInt256) (S : System) (a : AuthCallAtHead) : Prop :=
  CheckFlowId enc a.flow ∧ a.flow.preimage.settlementLayerChainId = l1
    ∧ a.missing ∈ pinLegs a.flow.preimage
    ∧ LegRefundableBy h z0 hl cv S (pinFlow a.flow) a.missing a.batch a.proof
    ∧ a.marked ∈ a.flow.preimage.legBundleHashes

/-- A call that takes a flow preimage. At head that is all three: `append`,
`requireFlowFinalized`, `authorizeRefund`. -/
inductive CallAtHead where
  | append (a : AppendCall)
  | execute (e : ExecCallAtHead)
  | authorize (a : AuthCallAtHead)

/-- The preimage the call took. -/
def CallAtHead.preimage : CallAtHead → FlowPreimage
  | .append a => a.preimage
  | .execute e => e.flow.preimage
  | .authorize a => a.flow.preimage

/-- The flow id the call computed (`append`) or checked (the other two). -/
def CallAtHead.flowId (enc : PreimageHash) : CallAtHead → UInt256
  | .append a => enc a.preimage
  | .execute e => e.flow.flowId
  | .authorize a => a.flow.flowId

/-- The `append` call, when the call is one. -/
def CallAtHead.appendCall? : CallAtHead → Option AppendCall
  | .append a => some a
  | _ => none

/-- The `append` calls of a log, most recent first. -/
def appendCalls (log : List CallAtHead) : List AppendCall :=
  log.filterMap CallAtHead.appendCall?

/-- The obligations the `append` calls of a log committed, most recent first. -/
def appendLog (enc : PreimageHash) (log : List CallAtHead) : List Obligation :=
  (appendCalls log).map (AppendCall.obligation enc)

/-- The obligations the `append` calls of a log committed on chain `c`, most recent first. -/
def chainLog (enc : PreimageHash) (c : Chain) (log : List CallAtHead) : List Obligation :=
  (appendLog enc log).filter (fun o => o.chain = c)

/-- **A CLASH BETWEEN TWO PREIMAGES OF THE RUN'S OWN LOG.** -/
def LoggedPreimageClash (enc : PreimageHash) (log : List CallAtHead) : Prop :=
  ∃ k ∈ log, ∃ k' ∈ log, PreimageClash enc k.preimage k'.preimage

/-! ## The run -/

/-- **EVERY CHAIN'S CALLS, INTERLEAVED, AT HEAD.** `RunAtHead … X Y log`: from `X` the chains
reach `Y`, and `log` holds every call that took a preimage, most recent first.

* `append a`: `AppendSucceedsAtHead` on `a.chain`; the leg is `Committed` under `enc a.preimage`
  and its commit value inserted at `low`.
* `execute e`: `requireFlowFinalized` passed; no state changes.
* `authorize a`: `authorizeRefund`'s checks passed, and the leg `a.marked` of the presented
  flow is `Committed` in the manager of `a.chain`, the chain running the call; it is marked
  `Revertable` there.
* `claim`: `claimRefund` on a raw key, guarded by `Revertable`.
* `initL2`: the tree's `initL2`, which `setup` lets through only on an empty tree. -/
inductive RunAtHead (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (enc : PreimageHash) (l1 : UInt256) (S : System) (X : Chains) :
    Chains → List CallAtHead → Prop
  | refl : RunAtHead h z0 hl cv enc l1 S X X []
  | append {Y log} (a : AppendCall) {hint low : ℕ} : RunAtHead h z0 hl cv enc l1 S X Y log →
      AppendSucceedsAtHead enc cv l1 a.env a.chain (Y a.chain) a.bundleHash a.preimage hint low →
      RunAtHead h z0 hl cv enc l1 S X
        (Y.update a.chain ((Y a.chain).appended cv (enc a.preimage) a.bundleHash low))
        (.append a :: log)
  | execute {Y log} (e : ExecCallAtHead) : RunAtHead h z0 hl cv enc l1 S X Y log →
      e.Verified h z0 hl cv enc l1 S → RunAtHead h z0 hl cv enc l1 S X Y (.execute e :: log)
  | authorize {Y log} (a : AuthCallAtHead) : RunAtHead h z0 hl cv enc l1 S X Y log →
      a.Verified h z0 hl cv enc l1 S → AuthorizeGuard (Y a.chain).mgr a.flow.flowId a.marked →
      RunAtHead h z0 hl cv enc l1 S X
        (Y.update a.chain ⟨(Y a.chain).mgr.set a.flow.flowId a.marked .Revertable, (Y a.chain).tree⟩)
        (.authorize a :: log)
  | claim {Y log c f b} : RunAtHead h z0 hl cv enc l1 S X Y log → ClaimGuard (Y c).mgr f b →
      RunAtHead h z0 hl cv enc l1 S X (Y.update c ⟨(Y c).mgr.set f b .Reverted, (Y c).tree⟩) log
  | initL2 {Y log c} : RunAtHead h z0 hl cv enc l1 S X Y log → (Y c).tree.leafCount = 0 →
      RunAtHead h z0 hl cv enc l1 S X (Y.update c ⟨(Y c).mgr, reseed (Y c).tree⟩) log

end Contracts.FlowBindingAtHead
