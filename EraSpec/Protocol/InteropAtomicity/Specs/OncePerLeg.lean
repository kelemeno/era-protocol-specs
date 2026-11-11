import EraSpec.Protocol.InteropAtomicity.Specs.Refund
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearch

/-!
# Model: one source chain's `append` path, manager and tree together

`Contracts.AtomicFlowManager` (`Contracts/AtomicFlowManager/Specs/Model.lean`) models the
manager's per-leg state and has no tree.  `Contracts.InteropCommitmentTree`
(`Contracts/L2InteropCommitmentTree/Specs/Model.lean`) models the tree and has no manager.
`Contracts.Refund` (`Specs/Refund.lean`) composes the managers of all chains, again with no
tree: its `append` step is the manager's guard alone.  This file puts one chain's manager
and that chain's tree into one state, so that one `append` is one step of both.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.OncePerLeg`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg`.

Source paths below are relative to `l1-contracts/contracts/` in the pinned era-contracts
tree (`c67894b9`).

## The call path

`InteropCenter._dispatchBundle` (`interop/InteropCenter.sol:639-660`) computes
`bundleHash = encodeInteropBundleHash(block.chainid, abi.encode(bundle))` (`:644`). For an
atomic bundle it then calls `AtomicFlowManager.append(flowId, bundleHash, deadline,
lowNullifierIndex)` (`:650-655`). The sender supplies `flowId`, `deadline` and the hint.
`append` (`atomic-interop/AtomicFlowManager.sol:87-102`) runs

    if (_state[_flowId][_bundleHash] != LegState.Unset) revert ManagerLegAlreadyCommitted(..);  // :93
    _state[_flowId][_bundleHash] = LegState.Committed;                                           // :95
    uint256 value = AtomicInteropProof.commitValue(_flowId, _bundleHash);                        // :97
    (uint256 index, ) = IL2InteropCommitmentTree(commitmentTree()).insert(value, _lowNullifierIndex); // :99

and `L2InteropCommitmentTree.insert` (`atomic-interop/L2InteropCommitmentTree.sol:53-59`)
checks its caller (`:54`) and runs `IndexedMerkleTree.insert`
(`common/libraries/IndexedMerkleTree.sol:60-106`).  A revert anywhere reverts the whole
`append`.  So the step below needs the manager's guard and every check of the tree's
insert, and it makes both writes.

`commitValue(flowId, bundleHash)` is
`uint256(keccak256(abi.encode(ATOMIC_COMMIT_LEAF_TAG, flowId, bundleHash)))`
(`atomic-interop/libraries/AtomicInteropProof.sol:100-102`).  The tag is a constant
(`atomic-interop/IAtomicInterop.sol:91-94`).  The model keeps the commit value as the
free parameter `cv : CommitValue`.  Because the tag is fixed, two keys
`(flowId, bundleHash)` have distinct keccak preimages exactly when the keys differ.  So
`CommitClash cv o o'` (`Specs/Refund.lean`) is a keccak collision on the two named
preimages `abi.encode(TAG, o.flowId, o.bundleHash)` and
`abi.encode(TAG, o'.flowId, o'.bundleHash)`.

## Every call that writes the modelled state of these two contracts

* `append`. It is `onlyInteropCenter` (`AtomicFlowManager.sol:76-79, 92`), and the
  center's only call site is `_dispatchBundle` (`InteropCenter.sol:650`).
* `authorizeRefund` (`AtomicFlowManager.sol:134-162`).  It marks `Committed` legs
  `Revertable` one at a time (`:155-161`).  Both models below take one leg per step.  The
  one-chain `Steps` also drops the `_checkFlowId` and timeout checks, so it admits more
  authorizations than the contract.  The all-chains `SysSteps` keeps them, as
  `Contracts.Refund` does.
* `claimRefund` (`:165-180`) moves a leg from `Revertable` to `Reverted` (`:170, :175`).
  Its recovery calls (`:177`, `:219-230`) reach the manager's state only by re-entering
  these same entry points, which are steps of their own.  The manager's only other storage
  is `L1_CHAIN_ID` (`:53, :57`).
* `L2InteropCommitmentTree.initL2` (`:47-50`).  It is `onlyUpgrader`, and
  `IndexedMerkleTree.setup` reverts once the tree has a leaf (`IndexedMerkleTree.sol:43-45`).
  It is included as a step; after genesis it never fires.
* `L2InteropCommitmentTree.insert` reverts for every caller but the manager (`:54`).  The
  manager calls it only inside `append` (`AtomicFlowManager.sol:99`), so there is no
  separate tree-only step.

The manager's own `initL2` (`AtomicFlowManager.sol:69-74`) writes only `L1_CHAIN_ID`,
which is not modelled.  Also not modelled: upgrades of either contract by the complex
upgrader (`OPS-CONFIG`); events; the `FullMerkle` hash tree (only the list state is kept;
the dimensions are in `RunHeight`); and `append`'s `deadline` argument, which is only
emitted (`:101`).  Callers are fixed by the set of steps, as listed above, rather than
carried in the state.
-/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

/-- One source chain's atomic-interop storage: the flow manager's `_state`
(`AtomicFlowManager.sol:53`) and the commitment tree's list state
(`L2InteropCommitmentTree.sol:33`, `IndexedMerkleTree.sol:30-34`). -/
structure ChainState where
  mgr : Manager
  tree : Tree

/-- The state after the genesis upgrade.  `L2InteropCommitmentTree.initL2` has seeded the
tree with `setup` (`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:458-461`), and no leg
has been appended. -/
def genesis : ChainState := ⟨Contracts.AtomicFlowManager.empty, setup⟩

/-- The value `append` inserts for an obligation: `commitValue(flowId, bundleHash)`.  The
obligation's chain does not enter it (`AtomicInteropProof.sol:100-102`). -/
def commitOf (cv : CommitValue) (o : Obligation) : UInt256 := cv o.flowId o.bundleHash

/-- **`IndexedMerkleTree.insert(v, hint)` SUCCEEDS, LANDING ON LOW LEAF `low`.**  The
fields are the checks of `IndexedMerkleTree.sol:65-92`, in source order.  `search` is the
loop with the deployed `MAX_LOW_INDEX_SEARCH_ATTEMPTS` (`lowSearch`, topic `HintSearch`).
The writes (`:94-105`) are `Contracts.InteropCommitmentTree.insert T v low`. -/
structure InsertSucceeds (T : Tree) (v : UInt256) (hint low : ℕ) : Prop where
  /-- `IMTNotInitialized` (`:65-68`). -/
  initialized : Initialized T
  /-- `IMTValueZero` (`:69-71`). -/
  nonzero : v ≠ 0
  /-- `IMTValueAlreadyExists` (`:72-74`): the dedup gate. -/
  fresh : T.valueToIndex v = 0
  /-- `IMTLowLeafIndexOutOfBounds` (`:75-77`). -/
  hintInBounds : hint < T.leafCount
  /-- `IMTLowLeafValueTooLarge` (`:79-83`). -/
  hintBelow : (T.leaf hint).value < v
  /-- The search loop exits at `low` without `IMTLowLeafNextTooSmall` (`:85-92`). -/
  search : lowSearch T v maxLowIndexSearchAttempts hint = some low

/-- **`append(f, b, _, hint)` SUCCEEDS.**  The manager's guard and the tree's insert of the
commit value, in one transaction. -/
structure AppendSucceeds (cv : CommitValue) (s : ChainState) (f b : UInt256) (hint low : ℕ) :
    Prop where
  /-- `ManagerLegAlreadyCommitted` (`AtomicFlowManager.sol:93`). -/
  legUnset : AppendGuard s.mgr f b
  /-- The tree's `insert(commitValue(f, b), hint)` (`:97-99`). -/
  treeInsert : InsertSucceeds s.tree (cv f b) hint low

/-- The state after a successful `append`: the leg is `Committed` (`:95`) and the commit
value is inserted through low leaf `low` (`IndexedMerkleTree.sol:94-105`). -/
def ChainState.appended (s : ChainState) (cv : CommitValue) (f b : UInt256) (low : ℕ) :
    ChainState :=
  ⟨s.mgr.set f b .Committed, Contracts.InteropCommitmentTree.insert s.tree (cv f b) low⟩

/-- What `IndexedMerkleTree.setup` writes to the list state of an uninitialized tree
(`IndexedMerkleTree.sol:42-51`): `pushNewLeaf` makes the leaf count one, and the `{0,0,0}`
sentinel is written at index 0.  `valueToIndex` and the other leaves are untouched. -/
def reseed (T : Tree) : Tree where
  leafCount := 1
  leaf := fun i => if i = 0 then ⟨0, 0, 0⟩ else T.leaf i
  valueToIndex := T.valueToIndex

/-- **ONE CHAIN'S RUN, WITH ITS `append`s LOGGED.**  `Steps cv c s t log` says that chain
`c` reaches `t` from `s`, and that `log` lists the obligations its successful `append`
calls committed, most recent first.  The logged obligation of `append(f, b, ..)` is
`⟨f, b, c⟩`: the chain that escrowed is the chain that ran it.  Every interleaving of the
calls listed in the module header is a run. -/
inductive Steps (cv : CommitValue) (c : Chain) (s : ChainState) :
    ChainState → List Obligation → Prop
  | refl : Steps cv c s s []
  /-- `AtomicFlowManager.append(f, b, _, hint)`, called by the center. -/
  | append {t log f b hint low} : Steps cv c s t log → AppendSucceeds cv t f b hint low →
      Steps cv c s (t.appended cv f b low) (⟨f, b, c⟩ :: log)
  /-- One leg of `authorizeRefund`, with its flow-id and timeout checks dropped. -/
  | authorize {t log f b} : Steps cv c s t log → AuthorizeGuard t.mgr f b →
      Steps cv c s ⟨t.mgr.set f b .Revertable, t.tree⟩ log
  /-- `claimRefund`. -/
  | claim {t log f b} : Steps cv c s t log → ClaimGuard t.mgr f b →
      Steps cv c s ⟨t.mgr.set f b .Reverted, t.tree⟩ log
  /-- `L2InteropCommitmentTree.initL2`.  `setup` lets it through only on an empty tree. -/
  | initL2 {t log} : Steps cv c s t log → t.tree.leafCount = 0 →
      Steps cv c s ⟨t.mgr, reseed t.tree⟩ log

/-- **COUNTERFACTUAL: THE TREE'S `insert` WITHOUT ITS DEDUP CHECK.**  `InsertSucceeds`
minus `fresh` (`IMTValueAlreadyExists`, `IndexedMerkleTree.sol:72-74`).  This is not the
contract.  It is used only to show that this one check is what stops a commit-value clash
from occupying two indices
(`Contracts.AppendPath.Properties.WithoutDedupClashOccupiesTwoIndices`). -/
structure InsertSucceedsWithoutDedup (T : Tree) (v : UInt256) (hint low : ℕ) : Prop where
  initialized : Initialized T
  nonzero : v ≠ 0
  hintInBounds : hint < T.leafCount
  hintBelow : (T.leaf hint).value < v
  search : lowSearch T v maxLowIndexSearchAttempts hint = some low

/-! ## Every chain at once, with the refund layer's `authorizeRefund`

`Contracts.Refund.ReachLog` is the system of every chain's manager, with each
`authorizeRefund` checked as the contract checks it (`AuthCall.Verified`: `_checkFlowId`,
leg membership, and a timeout proof against the fixed history `S`).  Its `append` is the
manager's guard alone.  `SysSteps` is the same system with each chain's tree attached, so
its `append` is the composed one above.  It therefore has fewer runs than `ReachLog` (an
`append` whose insert reverts is not a step) and more structure.

The timeout evidence is still checked against the fixed history `S`, exactly as in
`Contracts.Refund`.  `S` is not tied to the live trees here; that is the operational
projection, which is open. -/

/-- Every source chain's atomic-interop storage. -/
abbrev Chains := Chain → ChainState

/-- Every chain after the genesis upgrade. -/
def genesisAll : Chains := fun _ => genesis

/-- Replace one chain's state. -/
def Chains.update (X : Chains) (c : Chain) (s : ChainState) : Chains :=
  fun x => if x = c then s else X x

/-- The managers alone: the state `Contracts.Refund` reasons about. -/
def Chains.mgrs (X : Chains) : Managers := fun c => (X c).mgr

/-- **EVERY CHAIN'S RUN, INTERLEAVED, WITH BOTH LOGS.**
`SysSteps h z0 hl cv fh S X Y log alog`: from `X` the chains reach `Y`.  `log` lists the
obligations the `append` calls committed, and `alog` the `authorizeRefund` calls, each
most recent first.  The authorize step is `Contracts.Refund.ReachLog.authorize` verbatim;
the others are the per-chain steps of `Steps`, on the chain they name. -/
inductive SysSteps (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (X : Chains) : Chains → List Obligation → List AuthCall → Prop
  | refl : SysSteps h z0 hl cv fh S X X [] []
  /-- `append(f, b, _, hint)` on chain `c`: the manager guard and the tree insert. -/
  | append {Y log alog c f b hint low} : SysSteps h z0 hl cv fh S X Y log alog →
      AppendSucceeds cv (Y c) f b hint low →
      SysSteps h z0 hl cv fh S X (Y.update c ((Y c).appended cv f b low)) (⟨f, b, c⟩ :: log) alog
  /-- `authorizeRefund`, marking the leg `a.leg` of the checked flow `a.flow` on its chain. -/
  | authorize {Y log alog} (a : AuthCall) : SysSteps h z0 hl cv fh S X Y log alog →
      a.Verified h z0 hl cv fh S →
      AuthorizeGuard (Y a.leg.chain).mgr a.flow.flowId a.leg.bundleHash →
      SysSteps h z0 hl cv fh S X
        (Y.update a.leg.chain
          ⟨(Y a.leg.chain).mgr.set a.flow.flowId a.leg.bundleHash .Revertable,
            (Y a.leg.chain).tree⟩)
        log (a :: alog)
  /-- `claimRefund` on chain `c`. -/
  | claim {Y log alog c f b} : SysSteps h z0 hl cv fh S X Y log alog →
      ClaimGuard (Y c).mgr f b →
      SysSteps h z0 hl cv fh S X (Y.update c ⟨(Y c).mgr.set f b .Reverted, (Y c).tree⟩) log alog
  /-- `L2InteropCommitmentTree.initL2` on chain `c`. -/
  | initL2 {Y log alog c} : SysSteps h z0 hl cv fh S X Y log alog →
      (Y c).tree.leafCount = 0 →
      SysSteps h z0 hl cv fh S X (Y.update c ⟨(Y c).mgr, reseed (Y c).tree⟩) log alog

end Contracts.AppendPath
