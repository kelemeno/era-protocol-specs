import EraSpec.Protocol.InteropAtomicity.Specs.Refund

/-!
# Model: `authorizeRefund` as deployed, on the chain it is called on

`Contracts.Refund` (`Specs/Refund.lean`) models `authorizeRefund` with two
simplifications that the source does not make.  This file removes both, and keeps
everything else of that model (the per-chain managers, `append`, `claim`, the fixed
multi-chain history `System`).

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.RefundFaithful`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.RefundFaithful`.

## 1. The calling chain is not the declared chain

`Refund.Step.authorize`, `ReachLog.authorize` (and `FlowBinding.RunLog.authorize`,
`AppendPath.SysSteps.authorize`) mark `(F.flowId, leg.bundleHash)` on `leg.chain`, the
leg's DECLARED source chain.  The contract marks its own storage:

    // atomic-interop/AtomicFlowManager.sol:155-161 (pin c67894b9)
    for (uint256 i = 0; i < n; ++i) {
        bytes32 h = _flow.legBundleHashes[i];
        if (_state[_flow.flowId][h] != LegState.Committed) continue;
        _state[_flow.flowId][h] = LegState.Revertable;
        ...
    }

`_state` is the manager of whatever chain the call runs on, and the loop never compares
`legSourceChainIds[i]` with `block.chainid`.  `append` (`:87-102`) takes the flow id as an
opaque value from `InteropCenter._dispatchBundle` (`interop/InteropCenter.sol:639-657`,
read from the sender's `atomicBundle` attribute), so a sender on chain `X` can commit
`(flowId, h)` under a flow whose preimage declares `h` on chain `Y`.  The comment at `:153-154` ("legs committed on other chains are not in
this manager's state") is true of legs committed on other chains, not of legs committed
here under a different declared chain.  `DeployedAuthCall.chain` is the calling chain
and `DeployedAuthCall.bundle` the bundle hash one iteration of the loop moves; nothing
ties either to a leg's declared chain.

## 2. The END branch is the check the contract runs, not its conclusion

`Refund.AuthCall.Verified` uses `Atomicity.LegRefundableBy`, whose END disjunct is
`IsLastOnTime`: "no later batch of the chain settled by the deadline".  That is the
conclusion of an argument, not a check.  `AtomicInteropProof.verifyTimeoutAbsence`
(`libraries/AtomicInteropProof.sol:171-196`) checks that the imported settlement-layer
root was created after the deadline, that the batch settled by it, and
`_verifyLastBatchInRoot` (`:217-230`): a zero-sibling test on the batch-leaf path that
the root's own authentication fixed.  Here the call carries that root, its per-chain
batch trees, and the path, and is verified by `Timeout.LegRefundableAcceptedBy`.  From the
contract's checks to `IsLastOnTime` takes two further facts, either of which can fail on
a real call: the root aggregates the missing leg's chain honestly (`StaleRootFor`
negated), and the last-batch path carries no collision (`PinnedBreak`, `PathCollision`).
`DeployedRefundBreak` has a case for each.

## Granularity

One `authorize` step is one iteration of the marking loop.  A transaction is the
sequence of its iterations on one chain; the model also admits interleavings of other
calls between iterations, which only adds runs.  The countermodels below use flows with
one bundle, where one step is the whole transaction.

## Model boundary

As in `Contracts.Refund`: the tree side is the fixed history `System`; `_checkFlowId`'s
sortedness and length checks are not modelled; the settlement layer is one clock.  The
per-call root and its batch trees are the prover's to name: that over-approximates what
a prover can present, which is the conservative direction for the exclusion results.
-/

namespace Contracts.RefundFaithful

open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier Contracts.InteropCommitmentTree
open Contracts.Atomicity Contracts.Timeout Contracts.AtomicFlowManager Contracts.Refund

/-- **ONE ITERATION OF `authorizeRefund`, AS DEPLOYED.**  The call
`authorizeRefund(flow, _missingLegIndex, _absence)` made on chain `chain`, and the bundle
hash `bundle` of `flow` whose `_state` slot on `chain` this iteration moves.  The timeout
evidence is what `_absence` carries: the batch, the IMT absence proof, the imported
settlement-layer root it resolves against with that root's per-chain batch trees, and on
the END branch the batch-leaf path `(pathSibs, pathLeaf)`. -/
structure DeployedAuthCall (h : Hash) (ze : UInt256) where
  /-- `block.chainid`: whose `_state` is written. -/
  chain : Chain
  /-- The flow `_checkFlowId` accepted. -/
  flow : Flow
  /-- `_flow.legBundleHashes[i]` for the iteration that writes. -/
  bundle : UInt256
  /-- The leg at `_missingLegIndex`, whose absence the proof shows. -/
  missing : FlowLeg
  /-- `_absence.batchNumber`. -/
  batch : ℕ
  /-- The IMT part of `_absence`. -/
  proof : ImtProof
  /-- `interopRoots[slChainId][slBlock]`, the imported root the proof resolves against. -/
  root : SlRoot
  /-- The per-chain batch trees inside `root`. -/
  backing : RootBacking h ze root
  /-- The batch-leaf path's siblings (END branch). -/
  pathSibs : ℕ → UInt256
  /-- The batch leaf the path starts from (END branch). -/
  pathLeaf : UInt256

/-- The obligation an iteration writes to: `_state[flow.flowId][bundle]` on `chain`. -/
def DeployedAuthCall.marks {h : Hash} {ze : UInt256} (a : DeployedAuthCall h ze) : Obligation :=
  ⟨a.flow.flowId, a.bundle, a.chain⟩

/-- **THE CHECKS `authorizeRefund` RUNS.**  `_checkFlowId`; the iterated bundle hash is one
of the flow's; the missing leg is one of the flow's; and `verifyTimeoutAbsence` passes as
run, against the missing leg's DECLARED source chain (the `ProofSourceChainMismatch`
comparison).  Nothing relates `chain` to any declared chain. -/
def DeployedAuthCall.Verified (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) {ze : UInt256} (a : DeployedAuthCall h ze) : Prop :=
  FlowIdChecked fh a.flow ∧ a.bundle ∈ a.flow.legs.map FlowLeg.bundleHash
    ∧ a.missing ∈ a.flow.legs
    ∧ LegRefundableAcceptedBy h z0 hl cv S a.backing a.flow a.missing a.batch a.proof
        a.pathSibs a.pathLeaf

/-- **EVERY INTERLEAVING OF EVERY CHAIN'S MANAGER CALLS, AS DEPLOYED, WITH BOTH LOGS.**
`DeployedRun … Ms Ns plog alog`: from `Ms` the managers reach `Ns`; `plog` lists the
obligations `append` committed and `alog` the `authorizeRefund` iterations, each most
recent first.  `append` and `claim` are `Refund.ReachLog`'s.  `authorize` writes the
CALLING chain's slot for the iterated bundle, guarded only by that slot being
`Committed` (the loop's `continue`). -/
inductive DeployedRun (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (ze : UInt256) :
    Managers → Managers → List Obligation → List (DeployedAuthCall h ze) → Prop
  | refl {Ms} : DeployedRun h z0 hl cv fh S ze Ms Ms [] []
  | append {Ms Ns plog alog c f b} : DeployedRun h z0 hl cv fh S ze Ms Ns plog alog →
      AppendGuard (Ns c) f b →
      DeployedRun h z0 hl cv fh S ze Ms (setAt Ns c ((Ns c).set f b .Committed))
        (⟨f, b, c⟩ :: plog) alog
  | authorize {Ms Ns plog alog} (a : DeployedAuthCall h ze) :
      DeployedRun h z0 hl cv fh S ze Ms Ns plog alog →
      a.Verified h z0 hl cv fh S →
      AuthorizeGuard (Ns a.chain) a.flow.flowId a.bundle →
      DeployedRun h z0 hl cv fh S ze Ms
        (setAt Ns a.chain ((Ns a.chain).set a.flow.flowId a.bundle .Revertable)) plog (a :: alog)
  | claim {Ms Ns plog alog c f b} : DeployedRun h z0 hl cv fh S ze Ms Ns plog alog →
      ClaimGuard (Ns c) f b →
      DeployedRun h z0 hl cv fh S ze Ms (setAt Ns c ((Ns c).set f b .Reverted)) plog alog

/-- **A STALE ROOT FOR ONE CHAIN.**  `R` omits a batch of chain `c` that had settled when
`R` was created: the chain-`c` instance of `¬ Timeout.Aggregates S R`.  This is the only
part of `Aggregates` the END branch's argument uses. -/
def StaleRootFor (S : System) (R : SlRoot) (c : Chain) : Prop :=
  ∃ m, S.time c m ≤ R.created ∧ R.upTo c < m

/-- **A LOCATED BREAK BEHIND A REFUND OF `o`, IN A DEPLOYED RUN.**  Relative to a flow `F`
executed on gate evidence `ev`: some iteration `a` in the run's authorize log wrote `o`,
and one of the following holds of `a`'s own evidence.

* `flowIdClash` — `a`'s flow is not `F`'s preimage, and `fh` collides on the two flows'
  `(legs, deadline)` preimages;
* `inclusion` — `a`'s flow is `F`, and `F`'s gate evidence for `a`'s missing leg carries a
  `TreeRootBreak`;
* `absence` — `a`'s flow is `F`, and `a`'s IMT absence proof carries a `TreeRootBreak` on
  the root its branch selects;
* `lastBatch` — `a`'s flow is `F`, `a` took the END branch, and its batch-leaf path pins a
  collision (`PinnedBreak` right after the batch, or a `PathCollision` on the path);
* `staleRoot` — `a`'s flow is `F`, `a` took the END branch, and `a`'s root omits a batch
  of the missing leg's chain that had settled when the root was created.

Only the first three exist in `Refund.RefundBreak`.  The last two are what the contract's
END branch accepts beyond `IsLastOnTime`.  Every witness is named by the run or by the
premises. -/
inductive DeployedRefundBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) (fh : FlowHash)
    (S : System) (ze : UInt256) (F : Flow) (ev : GateEvidence) (o : Obligation)
    (alog : List (DeployedAuthCall h ze)) : Prop
  | flowIdClash (a : DeployedAuthCall h ze) : a ∈ alog → a.marks = o →
      FlowIdClash fh F a.flow → DeployedRefundBreak h z0 hl fh S ze F ev o alog
  | inclusion (a : DeployedAuthCall h ze) : a ∈ alog → a.marks = o → a.flow = F →
      InclusionBreak h z0 hl S a.missing.chain (ev a.missing).1 (ev a.missing).2 →
      DeployedRefundBreak h z0 hl fh S ze F ev o alog
  | absence (a : DeployedAuthCall h ze) : a ∈ alog → a.marks = o → a.flow = F →
      AbsenceBreak h z0 hl S F.deadline a.missing.chain a.batch a.proof →
      DeployedRefundBreak h z0 hl fh S ze F ev o alog
  | lastBatch (a : DeployedAuthCall h ze) : a ∈ alog → a.marks = o → a.flow = F →
      EndBranchAccepted a.backing S a.missing.chain F.deadline a.batch a.pathSibs a.pathLeaf →
      (PinnedBreak h ze (a.backing.leaves a.missing.chain) a.batch
        ∨ PathCollision h ze (a.backing.leaves a.missing.chain) a.pathSibs 0
            (a.backing.height a.missing.chain) a.batch a.pathLeaf) →
      DeployedRefundBreak h z0 hl fh S ze F ev o alog
  | staleRoot (a : DeployedAuthCall h ze) : a ∈ alog → a.marks = o → a.flow = F →
      EndBranchAccepted a.backing S a.missing.chain F.deadline a.batch a.pathSibs a.pathLeaf →
      StaleRootFor S a.root a.missing.chain →
      DeployedRefundBreak h z0 hl fh S ze F ev o alog

/-! ## Concrete configurations, for the countermodels -/

/-- A one-leg flow declaring bundle `2` on chain `1`.  Used with a commitment of bundle `2`
on chain `0`: the leg is committed on a chain other than the one the flow declares. -/
def misdeclaredFlow : Flow where
  flowId := 1
  legs := [⟨1, 2⟩]
  deadline := 0

/-- The obligation chain `0`'s manager holds for `misdeclaredFlow`'s bundle. -/
def misdeclaredObligation : Obligation := ⟨1, 2, 0⟩

/-- The batch trees of `Timeout.staleRoot` (which holds batch 0 only): one batch leaf per
chain, at height 0. -/
def staleBacking (h : Hash) (ze : UInt256) : RootBacking h ze staleRoot where
  leaves := fun _ => [ze + 1]
  height := fun _ => 0
  upToLast := fun _ => rfl
  capacity := fun _ => by norm_num

/-- A one-leg flow on chain `0` with deadline `0`, for the stale-root countermodel. -/
def staleFlow : Flow where
  flowId := 0
  legs := [⟨0, 0⟩]
  deadline := 0

end Contracts.RefundFaithful
