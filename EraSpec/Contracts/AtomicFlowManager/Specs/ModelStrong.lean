import EraSpec.Contracts.AtomicFlowManager.Specs.Model


/-!
# Contract spec: `AtomicFlowManager`, with runs and reentrant claims

Definitions for `EraSpec.Contracts.AtomicFlowManager.Properties.ModelStrong`; the proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.ModelStrong`.  Source:
`contracts/atomic-interop/AtomicFlowManager.sol` at era-contracts
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (`l1-contracts/`).

## Why this file exists

Several docstrings in `EraSpec.Contracts.AtomicFlowManager.Properties.Model` make claims about runs or about
the order of operations inside `claimRefund`: "a refund requires a prior authorization", "no run can move a leg
more than three times", "had the order been reversed, ... a reentrant claim would pass its guard".  The
statements there are about one state.  `Reach` records only that a state is reachable and keeps no trace of the
run.  `Step.claim` is a single atomic transition with no external-call phase.  This file adds the two things those
claims need, without changing the machine.

* **Traces.**  `LegStep` is `Step` with a label: the operation and the leg it moved.  `LegRun` is `Reach` with
  the list of labels.  The properties file proves `Step M N ↔ ∃ e, LegStep M e N` and
  `Reach M N ↔ ∃ es, LegRun M es N`, so a trace only keeps what `Reach` forgets.

* **Reentrant claims.**  `NestedRun` runs manager calls one after another.  During each `claimRefund`, the
  bundle's recovery calls (`_recoverBundle`, `:219-230`) may call back into the manager, to any depth.  The order
  of `claimRefund`'s write relative to those calls is a parameter.  `writeFirst` is the deployed code: the write at
  `:175` comes before `_recoverBundle` at `:177`.  `writeAfter` is the counterfactual that the source comment at
  `:171-174` rules out.

As everywhere in this folder, only successful calls are modelled.  A call that reverts leaves no trace.  A
reverting outer call takes its callback down with it, so such an execution is simply absent.  Whether
`_recoverBundle` recovers at least one call (`:229`) is not modelled here.  Any claim may complete, which allows
more executions than the source does.  That is the safe direction for an upper bound on payouts.  The
counterfactual executions below need only claims that complete, which a bundle with one recovering call achieves.
-/

namespace Contracts.AtomicFlowManager.ModelStrong


/-! ## Traces -/

/-- The three operations that write `_state`: `append` (`:95`), one leg of `authorizeRefund`'s loop (`:159`), and
`claimRefund` (`:175`). -/
inductive LegOp
  | append
  | authorize
  | claim
deriving DecidableEq, Repr


/-- The state an operation requires of its leg: its guard (`:93`, `:158`, `:170`). -/
def LegOp.needs : LegOp → LegState
  | .append => .Unset
  | .authorize => .Committed
  | .claim => .Revertable


/-- The state an operation writes to its leg (`:95`, `:159`, `:175`). -/
def LegOp.writes : LegOp → LegState
  | .append => .Committed
  | .authorize => .Revertable
  | .claim => .Reverted


/-- One labelled step: the operation, and the leg `(flowId, bundleHash)` it moved. -/
structure LegEvent where
  op : LegOp
  flow : UInt256
  bundle : UInt256
deriving DecidableEq, Repr


/-- `Step`, labelled.  Each constructor is `Step`'s constructor of the same name, with the label it earns. -/
inductive LegStep : Manager → LegEvent → Manager → Prop
  | append {M f b} : AppendGuard M f b → LegStep M ⟨.append, f, b⟩ (M.set f b .Committed)
  | authorize {M f b} : AuthorizeGuard M f b → LegStep M ⟨.authorize, f, b⟩ (M.set f b .Revertable)
  | claim {M f b} : ClaimGuard M f b → LegStep M ⟨.claim, f, b⟩ (M.set f b .Reverted)


/-- A run together with its trace, first step first.  `Reach` is this with the trace forgotten. -/
inductive LegRun : Manager → List LegEvent → Manager → Prop
  | nil {M} : LegRun M [] M
  | cons {M e N es P} : LegStep M e N → LegRun N es P → LegRun M (e :: es) P


/-- The events of a trace that name leg `(f, b)`, in order. -/
def legTrace (f b : UInt256) (es : List LegEvent) : List LegEvent :=
  es.filter fun e => decide (e.flow = f ∧ e.bundle = b)


/-- The lifecycle's operations in order: entry `i` is the one that leaves rank `i`. -/
def lifecycle : List LegOp := [.append, .authorize, .claim]


/-- The operations that take a leg from `s` up to `t`, in order. -/
def opsBetween (s t : LegState) : List LegOp :=
  (lifecycle.drop (rank s)).take (rank t - rank s)


/-- The state event `e` leaves behind when it fires on `M`.  Every `LegStep M e N` has `N = applyEvent M e`, so
replaying a trace from its start state passes through the run's own states. -/
def applyEvent (M : Manager) (e : LegEvent) : Manager :=
  M.set e.flow e.bundle e.op.writes


/-- The number of steps of the trace `es`, replayed from `M`, that change leg `(f, b)`'s state. -/
def legChanges (f b : UInt256) : Manager → List LegEvent → ℕ
  | _, [] => 0
  | M, e :: es =>
    (if (applyEvent M e).legState f b = M.legState f b then 0 else 1) + legChanges f b (applyEvent M e) es


/-! ### A witness run

Leg `(0, 0)` is appended, then leg `(0, 1)`, then `(0, 0)` is authorized and claimed. -/

/-- The witness run's trace. -/
def witnessTrace : List LegEvent :=
  [⟨.append, 0, 0⟩, ⟨.append, 0, 1⟩, ⟨.authorize, 0, 0⟩, ⟨.claim, 0, 0⟩]

/-- After the first step: leg `(0, 0)` is `Committed`. -/
def witness₁ : Manager := empty.set 0 0 .Committed

/-- After the second: leg `(0, 1)` is `Committed` too. -/
def witness₂ : Manager := witness₁.set 0 1 .Committed

/-- After the third: leg `(0, 0)` is `Revertable`. -/
def witness₃ : Manager := witness₂.set 0 0 .Revertable

/-- After the fourth: leg `(0, 0)` is `Reverted`. -/
def witness₄ : Manager := witness₃.set 0 0 .Reverted


/-! ## Reentrant claims -/

/-- Where `claimRefund` writes the leg's new state, relative to `_recoverBundle`'s external calls. -/
inductive ClaimOrder
  /-- The deployed order: `_state[_flowId][bundleHash] = LegState.Reverted` (`:175`), then
  `_recoverBundle` (`:177`). -/
  | writeFirst
  /-- The order the source comment at `:171-174` rules out: `_recoverBundle` first, then the write. -/
  | writeAfter
deriving DecidableEq, Repr


/-- A leg key `(flowId, bundleHash)`. -/
abbrev LegKey := UInt256 × UInt256


/-- `NestedRun o M log N`: successful manager calls, one after another, from `M` to `N`, with `claimRefund`
ordered as `o`.  `log` lists the legs whose `claimRefund` completed, one entry per completed claim (so one per
payout), in the order the claims completed.

`append` (`:87-102`) and `authorizeRefund` (`:134-162`, one leg at a time as in `Step`) make no call that can
re-enter the manager and write state.  `append`'s only external call is the commitment tree's `insert`, a
system contract.  `authorizeRefund`'s proof checks (`libraries/AtomicInteropProof.sol`) are `view`, so their
calls to the system's root storage and message verifier cannot write.  `claimRefund` (`:165-180`) does make such
calls.  Its `callback` is whatever nested
sequence of manager calls the bundle's targets make during `_recoverBundle`, itself a `NestedRun`.  `rest` is what
runs after the claim returns. -/
inductive NestedRun (o : ClaimOrder) : Manager → List LegKey → Manager → Prop
  | nil {M} : NestedRun o M [] M
  | append {M f b log N} : AppendGuard M f b →
      NestedRun o (M.set f b .Committed) log N → NestedRun o M log N
  | authorize {M f b log N} : AuthorizeGuard M f b →
      NestedRun o (M.set f b .Revertable) log N → NestedRun o M log N
  /-- The deployed order: the guard, then the write, then the callback, which runs against the written state. -/
  | claimWriteFirst {M f b callback N₁ rest N} : o = .writeFirst → ClaimGuard M f b →
      NestedRun o (M.set f b .Reverted) callback N₁ → NestedRun o N₁ rest N →
      NestedRun o M (callback ++ (f, b) :: rest) N
  /-- The reversed order: the guard, then the callback, which runs against the unwritten state, then the write. -/
  | claimWriteAfter {M f b callback N₁ rest N} : o = .writeAfter → ClaimGuard M f b →
      NestedRun o M callback N₁ → NestedRun o (N₁.set f b .Reverted) rest N →
      NestedRun o M (callback ++ (f, b) :: rest) N


end Contracts.AtomicFlowManager.ModelStrong
