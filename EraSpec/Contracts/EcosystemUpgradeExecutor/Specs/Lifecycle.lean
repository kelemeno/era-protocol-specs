import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: the `EcosystemUpgradeExecutor` lifecycle and the timer its operation names

**Source commit.** The coordinator does **not** exist at `e561b9cc2`, the commit the
`ChainTypeManager` folder models: commit `f64622022d` ("an upgrade is one atomic call",
2026-10-14) deleted its stages, the pending-operation state and `GovernanceUpgradeTimer`,
and `469310c94e` (2026-10-17) deleted the coordinator itself. This model is pinned at the
last commit that has the staged coordinator with its timer, **`afa407085`**
(`afa4070854051db19da27c85ec23dca712a6554b`, 2026-10-14, the parent of `f64622022d`, an
ancestor of `e561b9cc2`) on branch `feat/upgrade-simplification` of the zksync-era
`contracts` repository. Every `file:line` below is at `afa407085`; paths are relative to
`l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.EcosystemUpgradeExecutor.Properties.Lifecycle` and are proved in
`EraSpec.Contracts.EcosystemUpgradeExecutor.Proofs.Lifecycle`.

## The coordinator (`upgrades/registry/executors/EcosystemUpgradeExecutor.sol`)

Storage: `pendingOperation` (:47), `pendingStage` (:50, `None | Prepared | Executed`),
`pendingManifestHash` (:53). Every stage is `onlyOwner`.

* `stage0(op)` (:93-118):

        if (address(pendingOperation) != address(0)) { revert UpgradeLifecycleBusy(...); } // :94-96
        address(_operation).requireCode();                                       // :97
        _operation.validate();                                                    // :98
        pendingOperation = _operation; pendingStage = UpgradeStage.Prepared;      // :103-104
        ctmExecutor.beginOperation(_operation, m);                                // :115
        GovernanceUpgradeTimer(m.timer).startTimer();                             // :116

* `stage1(op)` (:124-135):

        OperationManifest memory m = _requirePending(_operation, UpgradeStage.Prepared); // :125
        GovernanceUpgradeTimer(m.timer).checkDeadline();                          // :126
        pendingStage = UpgradeStage.Executed;                                     // :129
        ctmExecutor.applyOperation(m);                                            // :133

* `stage2(op)` (:143-154):

        OperationManifest memory m = _requirePending(_operation, UpgradeStage.Executed); // :144
        GovernanceUpgradeTimer(m.timer).checkDeadline();                          // :145
        delete pendingOperation; pendingStage = UpgradeStage.None;                // :146-147
        ctmExecutor.completeOperation();                                          // :152

* `abandonPendingOperation(_)` (:160-179):

        if (address(operation) == address(0)) { revert NoPendingOperation(); }    // :162-164
        delete pendingOperation; pendingStage = UpgradeStage.None;                // :166-167
        ctmExecutor.abandonOperation();                                           // :174

* `_requirePending(op, expected)` (:184-201):

        if (address(pendingOperation) != address(_operation)) { revert OperationNotPending(...); } // :188-190
        if (pendingStage != _expected) { revert UpgradeStageOutOfOrder(...); }    // :191-193

## What the coordinator checks about the timer

Only this: the operation's manifest names a nonzero `timer`
(`objects/EcosystemUpgradeOperation.sol:30-32`), it has code (`validate`, :76), and the
three calls above — `startTimer()` at stage 0, `checkDeadline()` at stages 1 and 2 — return
without reverting. It never reads `INITIAL_DELAY`, never checks that the code is a
`GovernanceUpgradeTimer`, and never checks `TIMER_GOVERNANCE`. The manifest's field
comment (`upgrades/registry/RegistryTypes.sol:190-193`) says "Mandatory — every operation
has an execution delay"; the stage docs (`docs/upgrade-stage-lifecycle.md:95-96`) say "No
minimum delay is enforced on-chain, and a zero `INITIAL_DELAY` — all three stages in one
block — is acceptable".

A high-level call to an address with code and a function with no return values succeeds
whenever the callee does not revert, so **any contract whose fallback does not revert**
passes all three calls (`TimerCode.permissive`).

## `GovernanceUpgradeTimer` (`upgrades/GovernanceUpgradeTimer.sol`)

    modifier onlyTimerAdmin() { if (msg.sender != TIMER_GOVERNANCE) { revert CallerNotTimerAdmin(); } _; } // :65-70
    function startTimer() external onlyTimerAdmin {                                // :75
        if (deadline != 0) { revert TimerAlreadyStarted(); }                       // :76-78
        deadline = block.timestamp + INITIAL_DELAY;                                // :80
        maxDeadline = deadline + MAX_ADDITIONAL_DELAY; }                           // :81
    function checkDeadline() external view {                                       // :88
        if (deadline == 0) { revert TimerNotStarted(); }                           // :89-91
        if (block.timestamp < deadline) { revert DeadlineNotYetPassed(); } }       // :92-94
    function changeDeadline(uint256 newDeadline) external onlyOwner {              // :107
        if (newDeadline <= deadline) { revert NewDeadlineNotGreaterThanCurrent(); } // :108-110
        if (newDeadline > maxDeadline) { revert NewDeadlineExceedsMaxDeadline(); }  // :111-113
        deadline = newDeadline; }                                                  // :115

## The CTM domain's reservation (`executors/DomainUpgradeExecutorBase.sol`, `CTMUpgradeExecutor.sol`)

`beginOperation` (`DomainUpgradeExecutorBase.sol:43-51`) requires the domain idle (:47,
`_requireIdle` :86-90) and records `activeOperation`; `completeOperation` (:54-59) and
`abandonOperation` (:62-66) require it active (`_requireActive` :79-84) and clear it. All
three, and `CTMUpgradeExecutor.applyOperation` (`CTMUpgradeExecutor.sol:87-106`, which
also requires it active, :88), are `onlyCoordinator` (`DomainUpgradeExecutorBase.sol:22-27`).

## `forward`

The coordinator inherits `UpgradeExecutorBase.forward(Call[])` (`governance/UpgradeExecutorBase.sol:32-46`):
an owner-only raw `call` from the coordinator's address. Through it the coordinator's owner
can call the CTM executor's `onlyCoordinator` functions directly, and, when
`TIMER_GOVERNANCE` is the coordinator, `startTimer()`. These are the `forward*` labels.

## Modelling choices

* **A revert is the absence of a step.** Reject-only checks that read nothing modelled are
  omitted: the manifest-hash checks (:101, :195-200), `validate()` beyond the timer's code,
  the CTM leg's own checks (`_reserveLeg`, rows, transition edges, published bytecodes),
  the migration pause, and checked-arithmetic overflow in the timer (`ℕ` here). Omitting a
  rejecting check only adds runs.
* **The core domain is not modelled.** Its reservation (`CORE_EXECUTOR.beginOperation`,
  :107-109, and its completion and abandonment) only adds reverts.
* **Bindings are fixed.** The CTM executor's `coordinator` is this coordinator and the
  coordinator's `ctmExecutor` is that executor. `setCTMExecutor` (:63-87) and
  `setCoordinator` (`DomainUpgradeExecutorBase.sol:36-40`) are refused while an operation
  is pending; they are not modelled.
* **Timers are their code** (`TimerCode`): a `GovernanceUpgradeTimer` with its immutables,
  a permissive contract, or something on which every call reverts (no code included). Other
  timer code is not modelled. Every `GovernanceUpgradeTimer` keeps `deadline` and
  `maxDeadline`; its `TIMER_GOVERNANCE` may start it directly and its owner may extend it,
  at any time (`startByGovernance`, `changeDeadline`).
* **Time** is the block timestamp, `Sys.now`; it only increases (`tick`).
* **Ghosts**: `preparedAt` is the timestamp of the stage 0 that set the pending operation;
  `legAppliedAt op` is when the CTM leg (`applyOperation`) last ran with `op` reserved.
-/

namespace Contracts.EcosystemUpgradeExecutor

open Clear

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- Point update of a mapping. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- `IEcosystemUpgradeExecutor.UpgradeStage`. -/
inductive Stage
  | none
  | prepared
  | executed
deriving DecidableEq

/-- What runs at a timer address. -/
inductive TimerCode
  /-- A `GovernanceUpgradeTimer(INITIAL_DELAY, MAX_ADDITIONAL_DELAY, TIMER_GOVERNANCE, _)`. -/
  | governance (initialDelay maxAdditionalDelay : ℕ) (timerGovernance : Address)
  /-- Code on which `startTimer()` and `checkDeadline()` return without reverting and
  without effect, e.g. any contract with a non-reverting `fallback`. -/
  | permissive
  /-- Code on which every call reverts; no code at all is this case. -/
  | reverting
deriving DecidableEq

/-- The deployed objects. -/
structure Config where
  /-- The coordinator's own address. -/
  C : Address
  /-- An operation's manifest `timer`, `none` if the address is not an operation. -/
  opTimer : Address → Option Address
  /-- The code at each address, read as a timer. -/
  timer : Address → TimerCode

/-- The coordinator, the CTM domain's reservation, the timers, and the clock. -/
structure Sys where
  /-- `block.timestamp`. -/
  now : ℕ
  /-- `pendingOperation`; zero for none. -/
  pending : Address
  /-- `pendingStage`. -/
  stage : Stage
  /-- Each `GovernanceUpgradeTimer`'s `deadline`; zero until started. -/
  deadline : Address → ℕ
  /-- Each `GovernanceUpgradeTimer`'s `maxDeadline`. -/
  maxDeadline : Address → ℕ
  /-- The CTM executor's `activeOperation`; zero for none. -/
  active : Address
  /-- Ghost: when the stage 0 that set `pending` ran. -/
  preparedAt : ℕ
  /-- Ghost: when the CTM leg last ran with each operation reserved. -/
  legAppliedAt : Address → Option ℕ

/-- `startTimer()` called by the coordinator succeeds on timer `t` (:75-78; the caller
check :65-70 needs `TIMER_GOVERNANCE` to be the coordinator). -/
def StartOk (K : Config) (s : Sys) (t : Address) : Prop :=
  match K.timer t with
  | .governance _ _ g => g = K.C ∧ s.deadline t = 0
  | .permissive => True
  | .reverting => False

/-- What `startTimer()` leaves (:80-81). -/
def startEffect (K : Config) (s : Sys) (t : Address) : Sys :=
  match K.timer t with
  | .governance d a _ =>
      { s with deadline := upd s.deadline t (s.now + d),
               maxDeadline := upd s.maxDeadline t (s.now + d + a) }
  | _ => s

/-- `checkDeadline()` succeeds on timer `t` (:88-95). -/
def DeadlinePassed (K : Config) (s : Sys) (t : Address) : Prop :=
  match K.timer t with
  | .governance _ _ _ => s.deadline t ≠ 0 ∧ s.deadline t ≤ s.now
  | .permissive => True
  | .reverting => False

/-- What happens. -/
inductive Label
  /-- The clock moves to `t`. -/
  | tick (t : ℕ)
  /-- `stage0(op)`. -/
  | stage0 (op : Address)
  /-- `stage1(op)`. -/
  | stage1 (op : Address)
  /-- `stage2(op)`. -/
  | stage2 (op : Address)
  /-- `abandonPendingOperation(_)`. -/
  | abandon
  /-- A timer's `TIMER_GOVERNANCE` calls its `startTimer()` directly. -/
  | startByGovernance (t : Address)
  /-- A timer's owner calls `changeDeadline(x)`. -/
  | changeDeadline (t : Address) (x : ℕ)
  /-- The coordinator's owner forwards `ctmExecutor.beginOperation(op, _)`. -/
  | forwardBegin (op : Address)
  /-- The coordinator's owner forwards `ctmExecutor.applyOperation(_)`. -/
  | forwardApply
  /-- The coordinator's owner forwards `ctmExecutor.completeOperation()` or
  `abandonOperation()`. -/
  | forwardRelease
deriving DecidableEq

/-- The `forward` paths. -/
def Label.isForward : Label → Prop
  | .forwardBegin _ => True
  | .forwardApply => True
  | .forwardRelease => True
  | _ => False

/-- One successful transaction. -/
inductive Step (K : Config) : Sys → Label → Sys → Prop
  | tick {s : Sys} {t : ℕ} : s.now < t → Step K s (.tick t) { s with now := t }
  /-- `stage0` (:93-118): the slot is free (:94-96), the operation has code (:97) and
  names a timer with code (`EcosystemUpgradeOperation.sol:76`), the CTM domain is idle
  (`DomainUpgradeExecutorBase.sol:47`), and the timer starts (:116). -/
  | stage0 {s : Sys} {op t : Address} :
      s.pending = 0 → op ≠ 0 → K.opTimer op = some t → s.active = 0 → StartOk K s t →
      Step K s (.stage0 op)
        { startEffect K s t with pending := op, stage := .prepared, active := op,
                                 preparedAt := s.now }
  /-- `stage1` (:124-135): pending at `Prepared` (:188-193), the deadline has passed
  (:126), and the CTM leg is reserved (`CTMUpgradeExecutor.sol:88`). -/
  | stage1 {s : Sys} {op t : Address} :
      s.pending = op → s.stage = .prepared → K.opTimer op = some t → DeadlinePassed K s t →
      s.active ≠ 0 →
      Step K s (.stage1 op)
        { s with stage := .executed, legAppliedAt := upd s.legAppliedAt s.active (some s.now) }
  /-- `stage2` (:143-154): pending at `Executed`, the deadline has passed (:145), and the
  reservation is released (`DomainUpgradeExecutorBase.sol:54-59`). -/
  | stage2 {s : Sys} {op t : Address} :
      s.pending = op → s.stage = .executed → K.opTimer op = some t → DeadlinePassed K s t →
      s.active ≠ 0 →
      Step K s (.stage2 op) { s with pending := 0, stage := .none, active := 0 }
  /-- `abandonPendingOperation` (:160-179): something is pending (:162-164) and the
  reservation is released (`DomainUpgradeExecutorBase.sol:62-66`). -/
  | abandon {s : Sys} :
      s.pending ≠ 0 → s.active ≠ 0 →
      Step K s .abandon { s with pending := 0, stage := .none, active := 0 }
  /-- `startTimer()` by `TIMER_GOVERNANCE` (`GovernanceUpgradeTimer.sol:75-84`). -/
  | startByGovernance {s : Sys} {t : Address} {d a : ℕ} {g : Address} :
      K.timer t = .governance d a g → s.deadline t = 0 →
      Step K s (.startByGovernance t)
        { s with deadline := upd s.deadline t (s.now + d),
                 maxDeadline := upd s.maxDeadline t (s.now + d + a) }
  /-- `changeDeadline(x)` by the timer's owner (`GovernanceUpgradeTimer.sol:107-118`). -/
  | changeDeadline {s : Sys} {t : Address} {x d a : ℕ} {g : Address} :
      K.timer t = .governance d a g → s.deadline t < x → x ≤ s.maxDeadline t →
      Step K s (.changeDeadline t x) { s with deadline := upd s.deadline t x }
  /-- `forward` → `beginOperation(op, _)` (`DomainUpgradeExecutorBase.sol:43-51`). -/
  | forwardBegin {s : Sys} {op : Address} :
      s.active = 0 → Step K s (.forwardBegin op) { s with active := op }
  /-- `forward` → `applyOperation(_)` (`CTMUpgradeExecutor.sol:87-106`). -/
  | forwardApply {s : Sys} :
      s.active ≠ 0 →
      Step K s .forwardApply { s with legAppliedAt := upd s.legAppliedAt s.active (some s.now) }
  /-- `forward` → `completeOperation()` / `abandonOperation()`. -/
  | forwardRelease {s : Sys} :
      s.active ≠ 0 → Step K s .forwardRelease { s with active := 0 }

/-- A sequence of successful transactions. -/
inductive Run (K : Config) : Sys → List Label → Sys → Prop
  | nil {s : Sys} : Run K s [] s
  | cons {s s' s'' : Sys} {l : Label} {ls : List Label} :
      Step K s l s' → Run K s' ls s'' → Run K s (l :: ls) s''

/-- No operation is mid-lifecycle and the CTM domain is not reserved. -/
def Idle (s : Sys) : Prop := s.pending = 0 ∧ s.stage = .none ∧ s.active = 0

/-- How a step may move the lifecycle slot `(pendingOperation, pendingStage)`: not at all;
from free to an operation at `Prepared`; from `Prepared` to `Executed` for the same
operation; from `Executed` to free; or from occupied to free. -/
def Advances (s s' : Sys) : Prop :=
  (s'.pending = s.pending ∧ s'.stage = s.stage) ∨
  (s.pending = 0 ∧ s.stage = .none ∧ s'.pending ≠ 0 ∧ s'.stage = .prepared) ∨
  (s.pending ≠ 0 ∧ s.stage = .prepared ∧ s'.pending = s.pending ∧ s'.stage = .executed) ∨
  (s.pending ≠ 0 ∧ s'.pending = 0 ∧ s'.stage = .none)

/-! ## Witness data

Coordinator `10`. Operation `1` names timer `7`, a `GovernanceUpgradeTimer` with zero
delay; operation `2` names timer `8`, one with a 10-second delay; operation `3` names
timer `9`, a permissive contract. All three timers are bound to the coordinator. -/

/-- Operation timers. -/
def wOpTimer : Address → Option Address := fun a =>
  if a = 1 then some 7 else if a = 2 then some 8 else if a = 3 then some 9 else none

/-- Timer code. -/
def wTimer : Address → TimerCode := fun a =>
  if a = 7 then .governance 0 1209600 10
  else if a = 8 then .governance 10 1209600 10
  else if a = 9 then .permissive
  else .reverting

/-- The witness configuration. -/
def wK : Config := ⟨10, wOpTimer, wTimer⟩

/-- Idle at time `100`, no timer started. -/
def w0 : Sys := ⟨100, 0, .none, fun _ => 0, fun _ => 0, 0, 0, fun _ => none⟩

end Contracts.EcosystemUpgradeExecutor
