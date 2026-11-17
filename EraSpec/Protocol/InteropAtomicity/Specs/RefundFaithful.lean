import EraSpec.Protocol.InteropAtomicity.Specs.Refund
import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeafFaithful

/-!
# Model: `authorizeRefund` as it runs, on the chain that calls it

`Contracts.Refund` (`Specs/Refund.lean`) models `authorizeRefund` with two simplifications
that the source does not make.  This file removes both, and keeps the rest of that model:
the per-chain managers, `append`, `claim`, and the fixed multi-chain history `System`.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.RefundFaithful`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.RefundFaithful`.

Sources: era-contracts `c67894b9`, under `l1-contracts/contracts/`.

## 1. The slot written is the calling chain's

`Refund.ReachLog.authorize` (and `Refund.Step.authorize`, `FlowBinding.RunLog.authorize`,
`AppendPath.SysSteps.authorize`) writes `(F.flowId, leg.bundleHash)` in the manager of
`leg.chain`, the leg's DECLARED source chain.  The contract writes its own storage:

    // atomic-interop/AtomicFlowManager.sol:155-161
    for (uint256 i = 0; i < n; ++i) {
        bytes32 h = _flow.legBundleHashes[i];
        if (_state[_flow.flowId][h] != LegState.Committed) continue;
        _state[_flow.flowId][h] = LegState.Revertable;
        ...
    }

`_state` is the storage of the manager on the chain the call runs on, and nothing in
`authorizeRefund` (`:134-162`) compares a `legSourceChainIds[i]` with `block.chainid`.
`append` (`:87-102`, callable only by the interop center) checks that the slot is `Unset`
and reads no flow preimage; the flow id it is given is the sender's
(`InteropCenter._dispatchBundle`, `interop/InteropCenter.sol:643-655`).  So a sender on
chain `X` can commit `(flowId, h)` under a flow whose preimage declares `h` on chain
`Y ≠ X`, and an `authorizeRefund` call on `X` then writes `X`'s slot.  The comment at
`:153-154` ("legs committed on other chains are not in this manager's state") is about
legs committed on other chains, not about legs committed here under another declared
chain.

`DeployedAuthCall.chain` is the calling chain, and `DeployedAuthCall.bundle` the bundle
hash whose slot one iteration of the loop writes.  Nothing ties either to a declared chain.

## 2. The END branch is the check the contract runs

`Refund.AuthCall.Verified` uses `Atomicity.LegRefundableBy`, whose END disjunct is
`IsLastOnTime` ("no later batch of the chain settled by the deadline"): the conclusion of an
argument, not a check.  `AtomicInteropProof.verifyTimeoutAbsence`
(`atomic-interop/libraries/AtomicInteropProof.sol:152-206`) checks that the imported
settlement-layer root exists and was created after the deadline (`:171-179`); on the END
branch, that the batch settled by the deadline (`:190-192`) and `_verifyLastBatchInRoot`
(`:195`, `:217-230`), a zero-sibling test over the batch-leaf path, whose length and mask
are the prover's; and `verifyNonInclusion` (`:198-205`).

Here a call carries that root, its per-chain batch trees (`Timeout.RootBacking`) and the
batch-leaf path `(pathLen, pathSibs, pathLeaf)`.  Its END branch is `DeployedEndBranch`,
whose last-batch check is `MerkleSpec.LastLeafFaithful.LastBatchPathAccepted`: the
submitted length is free and the index need not be an occupied leaf.  That drops the two
restrictions `Timeout.LastBatchAccepted` adds (see its Correction (LastLeafFaithful) note),
so every submission `Timeout.LegRefundableAcceptedBy` accepts is accepted here, at the
chain tree's own height (`Properties.AcceptedByIsDeployedTimeout`).

From these checks to `IsLastOnTime` takes two facts the contract does not check: that the
root aggregates every batch of the missing leg's chain that settled before it was created
(`StaleRootFor` negated: the per-chain half of `Timeout.Aggregates`, ASSUMPTIONS.md
`PROTO-AGGREGATES`), and that the batch-leaf path is the last leaf at the chain tree's
height (`MerkleSpec.LastLeafFaithful.LastLeafAnyLengthBreak` negated).
`DeployedRefundBreak` has a case for each.

## Granularity

One `authorize` step is one writing iteration of the loop.  A call is the sequence of its
writing iterations on one chain, all with the same checked evidence; an iteration that
skips writes nothing.  The model also admits other calls between the iterations of one
call, which only adds runs.  The countermodels use one-bundle flows, where one step is the
whole call.

## Model boundary

* As in `Contracts.Refund`: the tree side is the fixed history `System`, not tied to the
  `append` log.  `_checkSettlementLayerIsL1` (`:136`, `:236-240`) and `_checkFlowId`'s
  sortedness and length checks (`:248-254`) are not modelled; they only reject.
  `FlowIdChecked` keeps the hash comparison (`:255-258`).
* As in `Contracts.Timeout`: an absence proof is checked against the missing leg's source
  chain's true BEGIN or END IMT root at the batch.  `_authenticateRoot` (`:256-290`) is not
  modelled: not the settlement proof, not the settlement-layer id match (`:167-169`), and
  not that the batch lies inside the root on the BEGIN branch.  The root and its batch
  trees are the call's own fields, so the prover names them; that the root is imported on
  the calling chain is not modelled either.
* The batch-leaf path's position (its mask) is identified with `_absence.batchNumber`, and
  `RootBacking` reads chain-tree leaf `i` as batch `i`.  That needs first pushed batch 0 and
  contiguous pushes (`PROTO-CONTIGUOUS-PUSH`; the Correction (LastBatchInRootOffset) note
  on `Timeout.RootBacking`), and a batch-leaf hash that binds the batch number, which
  `MessageHashing.batchLeafHash` hashes in.  The claimed batch-leaf hash `pathLeaf` is
  free, as in `LastLeafFaithful`.

The prover-named roots and the omitted reject-only checks admit more calls than the
contract (the conservative direction for the exclusion results).  The identifications in
the last bullet, and the honest root authentication in the second, admit fewer.

## Current heads

At `main` `70096e2ea` and `draft/v0.35.0` `b17415d20` the marking loop is unchanged
(`AtomicFlowManager.sol:233-243`, resp. `:236-246`), but `append` takes the flow preimage
and reverts with `ManagerCommittedLegSourceChainMismatch` unless the preimage declares the
committing chain for the committed bundle (`:140-146`, resp. `:141-147`).  So there the
misdeclared commitment of `Properties.MisdeclaredLegRefundedOnlyInDeployedModel` needs two
flow preimages with one flow id.  This is argued from source; the heads are not modelled.
They also add checks this file does not have (`ManagerMissingLegIndexOutOfRange`, the
preimage version, `MAX_ATOMIC_FLOW_LEGS`, and at `b17415d20` `_checkLegSourceAllowed`).
-/

namespace Contracts.RefundFaithful

open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.LastLeafFaithful MerkleSpec.Verifier
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager Contracts.Refund

/-! ## The timeout check as the contract runs it -/

/-- **`verifyTimeoutAbsence`'s END branch, AS RUN.**  For chain `c`, deadline `D` and batch
`N`, against root `R` with batch trees `B`: the root was created after the deadline
(`ProofInteropRootNotAfterDeadline`), the batch settled by it
(`ProofTimeoutBranchMismatch(false, …)`), and `_verifyLastBatchInRoot` passed on the
submitted batch-leaf path, of length `k`, siblings `sibs` and claimed leaf hash `x`, at
position `N`.

Unlike `Timeout.EndBranchAccepted`, `k` need not be the chain tree's height and `N` need not
be an occupied leaf: neither is checked by the contract (`LastBatchPathAccepted`). -/
structure DeployedEndBranch {h : Hash} {ze : UInt256} {R : SlRoot} (B : RootBacking h ze R)
    (S : System) (c : Chain) (D N k : ℕ) (sibs : ℕ → UInt256) (x : UInt256) : Prop where
  /-- `ProofInteropRootNotAfterDeadline` (`AtomicInteropProof.sol:177-179`). -/
  rootAfterDeadline : D < R.created
  /-- `ProofTimeoutBranchMismatch(false, …)` (`:190-192`). -/
  onTime : S.time c N ≤ D
  /-- `_verifyLastBatchInRoot` (`:217-230`), with the path's length and mask the prover's. -/
  lastBatch : LastBatchPathAccepted h ze (B.leaves c) (B.height c) sibs k N x

/-- **`verifyTimeoutAbsence` AS RUN, ON ONE SUBMITTED PROOF**, for leg `leg` of flow `F`:
batch `N`, IMT absence proof `p`, and on the END branch the batch-leaf path `(k, sibs, x)`.
The BEGIN branch is `Timeout.LegRefundableAcceptedBy`'s; the END branch is
`DeployedEndBranch`. -/
def DeployedTimeoutAccepted (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) {ze : UInt256} {R : SlRoot} (B : RootBacking h ze R) (F : Flow)
    (leg : FlowLeg) (N : ℕ) (p : ImtProof) (k : ℕ) (sibs : ℕ → UInt256) (x : UInt256) : Prop :=
  (BeginBranchVerified S R leg.chain F.deadline N ∧
      AbsenceAccepted h z0 hl (beginTree S leg.chain N) (beginHeight S leg.chain N)
        (legValue cv F leg) p)
    ∨ (DeployedEndBranch B S leg.chain F.deadline N k sibs x ∧
        AbsenceAccepted h z0 hl (S.tree leg.chain N) (S.height leg.chain N)
          (legValue cv F leg) p)

/-! ## One writing iteration of `authorizeRefund` -/

/-- **ONE WRITING ITERATION OF `authorizeRefund`.**  The call
`authorizeRefund(flow, _missingLegIndex, _absence)` made on chain `chain`, and the bundle
hash `bundle` of `flow` whose `_state` slot on `chain` this iteration writes.  The timeout
evidence is what `_absence` carries: the batch, the IMT absence proof, the imported
settlement-layer root it resolves against with that root's per-chain batch trees, and on
the END branch the batch-leaf path `(pathLen, pathSibs, pathLeaf)`. -/
structure DeployedAuthCall (h : Hash) (ze : UInt256) where
  /-- `block.chainid`: the chain whose manager's `_state` is written. -/
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
  /-- The batch-leaf path's length, `batchLeafSiblings.length` (END branch). -/
  pathLen : ℕ
  /-- The batch-leaf path's siblings (END branch). -/
  pathSibs : ℕ → UInt256
  /-- The claimed batch-leaf hash the path starts from (END branch). -/
  pathLeaf : UInt256

/-- The slot an iteration writes: `_state[flow.flowId][bundle]` on `chain`. -/
def DeployedAuthCall.marks {h : Hash} {ze : UInt256} (a : DeployedAuthCall h ze) : Obligation :=
  ⟨a.flow.flowId, a.bundle, a.chain⟩

/-- **THE CHECKS AN ITERATION RESTS ON.**  `_checkFlowId`'s hash comparison; the written
bundle hash is one of the flow's; the missing leg is one of the flow's; and
`verifyTimeoutAbsence` passes as run (`DeployedTimeoutAccepted`) against the missing leg's
DECLARED source chain (the `ProofSourceChainMismatch` comparison, `:142-145`).  Nothing
relates `chain` to any declared chain.  See the module docstring for what is not
modelled. -/
def DeployedAuthCall.Verified (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) {ze : UInt256} (a : DeployedAuthCall h ze) : Prop :=
  FlowIdChecked fh a.flow ∧ a.bundle ∈ a.flow.legs.map FlowLeg.bundleHash
    ∧ a.missing ∈ a.flow.legs
    ∧ DeployedTimeoutAccepted h z0 hl cv S a.backing a.flow a.missing a.batch a.proof
        a.pathLen a.pathSibs a.pathLeaf

/-! ## Runs -/

/-- **EVERY INTERLEAVING OF EVERY CHAIN'S MANAGER CALLS, WITH `authorizeRefund` AS RUN.**
`DeployedRun … Ms Ns plog alog`: from `Ms` the managers reach `Ns`; `plog` lists the slots
`append` committed and `alog` the writing `authorizeRefund` iterations, each most recent
first.  `append` and `claim` are `Refund.ReachLog`'s.  `authorize` writes the CALLING
chain's slot for the iterated bundle hash, guarded only by that slot being `Committed`
(the loop's `continue`). -/
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

/-! ## Breaks -/

/-- **A STALE ROOT FOR ONE CHAIN.**  `R` omits a batch of chain `c` that had settled when `R`
was created: the chain-`c` instance of `¬ Timeout.Aggregates S R`. -/
def StaleRootFor (S : System) (R : SlRoot) (c : Chain) : Prop :=
  ∃ m, S.time c m ≤ R.created ∧ R.upTo c < m

/-- **A LOCATED BREAK BEHIND A REFUND OF SLOT `o`, IN A DEPLOYED RUN.**  Relative to a flow
`F` executed on gate evidence `ev`: some iteration `a` in the run's log wrote `o`, and one of
the following holds of `a`'s own evidence.

* `flowIdClash`: `a`'s flow is not `F`'s preimage, and `fh` collides on the two flows'
  `(legs, deadline)` preimages;
* `inclusion`: `a`'s flow is `F`, and `F`'s gate evidence for `a`'s missing leg carries a
  `TreeRootBreak`;
* `absence`: `a`'s flow is `F`, and `a`'s IMT absence proof carries a `TreeRootBreak` on the
  root its branch selects;
* `lastBatch`: `a`'s flow is `F`, `a` took the END branch, and its batch-leaf path is not
  the last leaf at the chain tree's height in one of the located ways of
  `LastLeafAnyLengthBreak` (a wrong length located by a `HeightBreak`, a padded index whose
  claimed leaf hash is the empty-entry constant, a `PinnedBreak` after the batch, or a
  `PathCollision` on the path);
* `staleRoot`: `a`'s flow is `F`, `a` took the END branch, and `a`'s root omits a batch of
  the missing leg's chain that had settled when the root was created.

Only the first three exist in `Refund.RefundBreak`; the last two are what the contract's
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
      DeployedEndBranch a.backing S a.missing.chain F.deadline a.batch a.pathLen a.pathSibs
        a.pathLeaf →
      LastLeafAnyLengthBreak h ze (a.backing.leaves a.missing.chain) a.pathSibs a.pathLen
        (a.backing.height a.missing.chain) a.batch a.pathLeaf →
      DeployedRefundBreak h z0 hl fh S ze F ev o alog
  | staleRoot (a : DeployedAuthCall h ze) : a ∈ alog → a.marks = o → a.flow = F →
      DeployedEndBranch a.backing S a.missing.chain F.deadline a.batch a.pathLen a.pathSibs
        a.pathLeaf →
      StaleRootFor S a.root a.missing.chain →
      DeployedRefundBreak h z0 hl fh S ze F ev o alog

/-! ## Concrete configurations, for the countermodels and witnesses -/

/-- A one-leg flow declaring bundle `2` on chain `1`, with id `1` and deadline `0`.  The
countermodel commits bundle `2` under it on chain `0`: a leg committed on a chain other
than the one the flow declares. -/
def misdeclaredFlow : Flow where
  flowId := 1
  legs := [⟨1, 2⟩]
  deadline := 0

/-- The slot chain `0`'s manager holds for `misdeclaredFlow`'s bundle. -/
def misdeclaredObligation : Obligation := ⟨1, 2, 0⟩

/-- The batch trees of `Timeout.staleRoot` (which holds batch 0 only): one batch leaf
`ze + 1` per chain, at height 0. -/
def staleBacking (h : Hash) (ze : UInt256) : RootBacking h ze staleRoot where
  leaves := fun _ => [ze + 1]
  height := fun _ => 0
  upToLast := fun _ => rfl
  capacity := fun _ => by norm_num

/-- A one-leg flow on chain `0` with id `0`, bundle hash `0` and deadline `0`, for the
stale-root countermodel. -/
def staleFlow : Flow where
  flowId := 0
  legs := [⟨0, 0⟩]
  deadline := 0

end Contracts.RefundFaithful
