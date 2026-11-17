import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearchAtHead

/-!
# Model at head: one source chain's `append` path, with the tree's unbounded walk

**Commit.** era-contracts `main` at `3605e82dbdca5b60bd7bc6bde14ebb52a6b09b73`.  The tree
side is the same on `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`.  Paths are
relative to `l1-contracts/contracts/`.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.OncePerLegAtHead`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLegAtHead`.

## What is re-modelled, and what is not

`Contracts.AppendPath.Steps` (`Specs/OncePerLeg.lean`, pin `c67894b9`) composes one chain's
`AtomicFlowManager._state` with its commitment tree.  Its `append` step needs the tree's
insert to pass the pin's five-hop search (`InsertSucceeds.search`).  At head the walk is
unbounded (`IndexedMerkleTree.sol:90-93`; `Contracts/L2InteropCommitmentTree/Specs/HintSearchAtHead.lean`),
so the head accepts appends whose stale hint needs more hops.  Those appends were outside
the pin model, so `OncePerLeg` and the other results stated over `Steps` did not cover them.
`StepsAtHead` and `SysStepsAtHead` below are `Steps` and `SysSteps` with the tree's insert
replaced by the head's (`InsertChecksAtHead`).  Every other step is unchanged.

The manager side of `append` is kept at the pin's abstraction: the guard
`_state[flowId][bundleHash] == Unset` (`AtomicFlowManager.sol:161-163` at `main`), the write
`Committed` (`:165`), and the insert of `commitValue(flowId, bundleHash)` (`:167-169`).  At
head `append` takes the flow preimage, recomputes `flowId` and adds reject-only checks before
the guard (`:108-159`: settlement layer, expired-flow gate, leg membership, the leg's declared
source chain, registered sources).  Those checks are modelled elsewhere (the append-binding
topic).  They only reject calls, so `StepsAtHead` over-approximates the head's manager side,
and every statement below that quantifies over all runs holds for the head's runs.  Liveness
statements here are about the tree insert and the `Unset` guard only.

The center's call site is still the single `append` call inside `_dispatchBundle`
(`interop/InteropCenter.sol:736` at `main`, `:742` at `draft/v0.35.0`).
`authorizeRefund` and `claimRefund` move legs as the pin models them.  `claimRefund` writes
`Reverted` before its external calls (`AtomicFlowManager.sol:257`).

## Why a separate relation

`StepsAtHead` admits strictly more calls than `Steps`: an append whose hint is more than five
hops from its landing index is a step here and not there.  It reaches no new state and no
new log, because the landing index, and hence the written state, does not depend on the hint
(`Contracts.InteropCommitmentTree.Properties.InsertAtHeadLandingHintIndependent`).  That is
`Contracts.AppendPath.Properties.StepsAtHeadIffSteps`.  It is what transfers the pin's
results here.
-/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

/-- **`append(.., hint)` SUCCEEDS AT HEAD, THE TREE LANDING ON `low`.**  The manager's `Unset`
guard and the tree's head insert of the commit value, in one transaction
(`AtomicFlowManager.sol:161-169`, `L2InteropCommitmentTree.sol:50-63`,
`IndexedMerkleTree.sol:65-107`). -/
structure AppendSucceedsAtHead (cv : CommitValue) (s : ChainState) (f b : UInt256)
    (hint low : ℕ) : Prop where
  /-- `ManagerLegAlreadyCommitted` (`AtomicFlowManager.sol:161-163`). -/
  legUnset : AppendGuard s.mgr f b
  /-- The tree's `insert(commitValue(f, b), hint)` at head (`:167-169`). -/
  treeInsert : InsertChecksAtHead s.tree (cv f b) hint low

/-- **ONE CHAIN'S RUN AT HEAD, WITH ITS `append`s LOGGED.**  `Steps` with the head's tree
insert.  The authorize, claim and `initL2` steps are `Steps`' own. -/
inductive StepsAtHead (cv : CommitValue) (c : Chain) (s : ChainState) :
    ChainState → List Obligation → Prop
  | refl : StepsAtHead cv c s s []
  /-- `AtomicFlowManager.append`, called by the center, with the head's tree insert. -/
  | append {t log f b hint low} : StepsAtHead cv c s t log →
      AppendSucceedsAtHead cv t f b hint low →
      StepsAtHead cv c s (t.appended cv f b low) (⟨f, b, c⟩ :: log)
  /-- One leg of `authorizeRefund`, with its flow-id and timeout checks dropped. -/
  | authorize {t log f b} : StepsAtHead cv c s t log → AuthorizeGuard t.mgr f b →
      StepsAtHead cv c s ⟨t.mgr.set f b .Revertable, t.tree⟩ log
  /-- `claimRefund`. -/
  | claim {t log f b} : StepsAtHead cv c s t log → ClaimGuard t.mgr f b →
      StepsAtHead cv c s ⟨t.mgr.set f b .Reverted, t.tree⟩ log
  /-- `L2InteropCommitmentTree.initL2`.  `setup` lets it through only on an empty tree. -/
  | initL2 {t log} : StepsAtHead cv c s t log → t.tree.leafCount = 0 →
      StepsAtHead cv c s ⟨t.mgr, reseed t.tree⟩ log

/-- **EVERY CHAIN'S RUN AT HEAD, INTERLEAVED, WITH BOTH LOGS.**  `SysSteps` with the head's
tree insert.  The authorize step is `Contracts.Refund.ReachLog.authorize` verbatim, as in
`SysSteps`. -/
inductive SysStepsAtHead (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (X : Chains) : Chains → List Obligation → List AuthCall → Prop
  | refl : SysStepsAtHead h z0 hl cv fh S X X [] []
  /-- `append(.., hint)` on chain `c`: the manager guard and the head's tree insert. -/
  | append {Y log alog c f b hint low} : SysStepsAtHead h z0 hl cv fh S X Y log alog →
      AppendSucceedsAtHead cv (Y c) f b hint low →
      SysStepsAtHead h z0 hl cv fh S X (Y.update c ((Y c).appended cv f b low))
        (⟨f, b, c⟩ :: log) alog
  /-- `authorizeRefund`, marking the leg `a.leg` of the checked flow `a.flow` on its chain. -/
  | authorize {Y log alog} (a : AuthCall) : SysStepsAtHead h z0 hl cv fh S X Y log alog →
      a.Verified h z0 hl cv fh S →
      AuthorizeGuard (Y a.leg.chain).mgr a.flow.flowId a.leg.bundleHash →
      SysStepsAtHead h z0 hl cv fh S X
        (Y.update a.leg.chain
          ⟨(Y a.leg.chain).mgr.set a.flow.flowId a.leg.bundleHash .Revertable,
            (Y a.leg.chain).tree⟩)
        log (a :: alog)
  /-- `claimRefund` on chain `c`. -/
  | claim {Y log alog c f b} : SysStepsAtHead h z0 hl cv fh S X Y log alog →
      ClaimGuard (Y c).mgr f b →
      SysStepsAtHead h z0 hl cv fh S X (Y.update c ⟨(Y c).mgr.set f b .Reverted, (Y c).tree⟩)
        log alog
  /-- `L2InteropCommitmentTree.initL2` on chain `c`. -/
  | initL2 {Y log alog c} : SysStepsAtHead h z0 hl cv fh S X Y log alog →
      (Y c).tree.leafCount = 0 →
      SysStepsAtHead h z0 hl cv fh S X (Y.update c ⟨(Y c).mgr, reseed (Y c).tree⟩) log alog

end Contracts.AppendPath
