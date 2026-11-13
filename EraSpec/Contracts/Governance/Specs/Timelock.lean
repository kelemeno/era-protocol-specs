import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `Governance` — the owner/security-council timelock

Source: era-contracts `draft/v0.35.0` at commit `d9f678900e1bc8286412b78f56d4a9f443983c29`,
file `l1-contracts/contracts/governance/Governance.sol` (cited `G:<line>`), and the inherited
OpenZeppelin v4.9 `Ownable2Step` at the pinned submodule `openzeppelin-contracts-v4`
`dc44c9f1a4c3b10af99492eed84f83ed244203f6` (`contracts/access/Ownable.sol`, cited `Own:<line>`,
and `contracts/access/Ownable2Step.sol`, cited `Own2:<line>`).

**This file is definitions only.** The statements are in
`EraSpec.Contracts.Governance.Properties.Timelock` and are proved in
`EraSpec.Contracts.Governance.Proofs.Timelock`.

## The state

    address private _owner;                                     // Own:21
    address private _pendingOwner;                              // Own2:20
    address public securityCouncil;                             // G:36
    mapping(bytes32 operationId => uint256 executionTimestamp) public timestamps;  // G:42
    uint256 public minDelay;                                    // G:45

plus `block.timestamp`, the environment's clock (`State.now`).  A timestamp of `0` is an unset
operation, `1` (`EXECUTED_PROPOSAL_TIMESTAMP`, G:32) a done one, anything else the time the
operation becomes ready (G:38-41, `getOperationState` G:121-132).

## Entry points

Every state-changing entry point is a step:

* `scheduleTransparent` (G:145-149) and `scheduleShadow` (G:158-161): `onlyOwner`, then `_schedule`
  (G:245-254): `OperationExists` if the id is an operation, `InvalidDelay` if `_delay < minDelay`,
  then `timestamps[id] = block.timestamp + _delay` (checked addition, so overflow reverts).
* `cancel` (G:170-176): `onlyOwner`, `OperationMustBePending` unless pending, then delete.
* `execute` (G:186-205): `onlyOwnerOrSecurityCouncil`, `_checkPredecessorDone` (G:276-280), the
  operation must be **ready**, then `_execute` (G:258-271) makes the calls, then readiness is
  checked **again**, then `timestamps[id] = 1`.
* `executeInstant` (G:211-230): `onlySecurityCouncil`, predecessor, **pending** (not necessarily
  ready), the calls, pending again, then `timestamps[id] = 1`.
* `updateDelay` (G:288-291) and `updateSecurityCouncil` (G:295-298): `onlySelf`.
* Inherited: `transferOwnership` (Own2:35-38, `onlyOwner`, sets the pending owner, no zero check),
  `acceptOwnership` (Own2:52-56, caller must be the pending owner) and `renounceOwnership`
  (Own:61-63, `onlyOwner`).  Both of the latter go through `_transferOwnership` (Own2:44-47,
  Own:78-82), which deletes the pending owner.
* The constructor (G:52-64, after `Ownable`'s constructor Own:28-30): `ZeroAddress` on a zero admin.

`receive()` (G:301) and the view functions write nothing modelled here and are not steps.

## Modelling choices

* **A revert is the absence of a step.**  `Entry.run` returns `none` on a revert; guards are
  tested in source order.
* **Re-entry.**  `_execute` calls arbitrary targets.  Those calls can call back into Governance,
  as Governance itself (that is how `onlySelf` functions are reached) or as any other address
  that some called contract uses.  `CallsWith` is therefore a finite sequence of re-entrant calls,
  each by an arbitrary caller, and an execution's inner calls are such a sequence.  Every call that
  does not re-enter Governance is invisible to this state.  A failing inner call reverts the whole
  execution (G:264-269), which is the absence of a step.  This over-approximates the source's
  runs: the calls are not tied to `_operation.calls`, so safety results hold for every target code.
* **One transaction, one clock.**  `block.timestamp` is constant inside a transaction; only a
  top-level `TopStepWith.tick` moves it, and never backwards.
* **External callers are never Governance.**  A top-level call has `caller ≠ e.self`: only
  Governance's own frame has `msg.sender == address(this)` (`VM-CALL`).
* **The hash is abstract.**  `Env.hashOp` is `keccak256(abi.encode(_operation))` (G:234-236).  No
  property assumes it injective; every statement is about operation ids.
* **The ghost log.**  Every step appends to a log: the source's events (G:60, 63, 148, 160, 175,
  204, 229, 289, 296; Own:81, Own2:37) with the block timestamp added to `scheduled` and
  `executed`, and the predecessor and kind added to `executed`.  The log is a ghost; nothing reads it.
* **The clock starts at 2.**  `ReachWith` starts at `block.timestamp ≥ 2`.  At a lower clock a
  schedule can write `0` or `1` (see `Properties.LowClockScheduleMarksDone`).
* **The check variant.**  `CallsWith false` drops the re-check after the calls (G:197-201,
  G:222-226).  It exists only for the countermodel `Properties.NoRecheckDoubleExecution`; the source
  is `CallsWith true` (`Calls`, `TopStep`, `Reach`, `TopRun`).
-/

namespace Contracts.Governance

abbrev Address := UInt256
/-- A `bytes32` operation id. -/
abbrev OpId := UInt256

/-- `Call` (`Common.sol`): one call of an operation.  Its effect on other contracts is not
modelled; its effect on Governance is the re-entrant calls of `CallsWith`. -/
structure CallData where
  target : Address
  value : UInt256
  data : List UInt8

/-- `Operation` (`IGovernance.sol`): the calls, the predecessor id, and a salt. -/
structure Operation where
  calls : List CallData
  predecessor : OpId
  salt : OpId

/-- The fixed environment: the contract's own address and `hashOperation` (G:234-236). -/
structure Env where
  self : Address
  hashOp : Operation → OpId

/-- The modelled storage, plus `block.timestamp`. -/
structure State where
  owner : Address
  pendingOwner : Address
  securityCouncil : Address
  timestamps : OpId → UInt256
  minDelay : UInt256
  /-- `block.timestamp`. -/
  now : UInt256

/-- `OperationState` (`IGovernance.sol`). -/
inductive OpState where
  | unset
  | waiting
  | ready
  | done
  deriving DecidableEq, Repr

/-- `getOperationState` (G:121-132). -/
def getOperationState (s : State) (id : OpId) : OpState :=
  if s.timestamps id = 0 then .unset
  else if s.timestamps id = 1 then .done
  else if s.now < s.timestamps id then .waiting
  else .ready

/-- `isOperation` (G:100-102). -/
def isOperation (s : State) (id : OpId) : Bool := getOperationState s id != .unset

/-- `isOperationPending` (G:105-108): waiting or ready. -/
def isOperationPending (s : State) (id : OpId) : Bool :=
  getOperationState s id == .waiting || getOperationState s id == .ready

/-- `isOperationReady` (G:111-113). -/
def isOperationReady (s : State) (id : OpId) : Bool := getOperationState s id == .ready

/-- `isOperationDone` (G:116-118). -/
def isOperationDone (s : State) (id : OpId) : Bool := getOperationState s id == .done

/-- `_checkPredecessorDone` (G:276-280) passes: a zero predecessor, or a done one. -/
def predecessorDone (s : State) (p : OpId) : Bool := p == 0 || isOperationDone s p

/-- The ghost log: the source's events, with the block timestamp added where a property needs it. -/
inductive Ev where
  /-- `TransparentOperationScheduled` (G:148) or `ShadowOperationScheduled` (G:160), with the block
  timestamp `at_` of the schedule. -/
  | scheduled (id : OpId) (at_ delay : UInt256)
  /-- `OperationCancelled` (G:175). -/
  | cancelled (id : OpId)
  /-- `OperationExecuted` (G:204, G:229), with the predecessor, whether it was `executeInstant`,
  and the block timestamp. -/
  | executed (id pred : OpId) (instant : Bool) (at_ : UInt256)
  /-- `ChangeMinDelay` (G:63, G:289). -/
  | minDelayChanged (old new : UInt256)
  /-- `ChangeSecurityCouncil` (G:60, G:296). -/
  | councilChanged (old new : Address)
  /-- `OwnershipTransferStarted` (Own2:37). -/
  | ownershipTransferStarted (owner pending : Address)
  /-- `OwnershipTransferred` (Own:81). -/
  | ownershipTransferred (old new : Address)
  deriving DecidableEq

/-- `_schedule` (G:245-254) on an already authorised call. -/
def schedule (s : State) (id : OpId) (delay : UInt256) : Option State :=
  if isOperation s id then none                         -- OperationExists (G:246-248)
  else if delay < s.minDelay then none                  -- InvalidDelay (G:249-251)
  else if s.now.val + delay.val < UInt256.size then     -- checked `+` (G:253)
    some { s with timestamps := Function.update s.timestamps id (s.now + delay) }
  else none

/-- The non-executing entry points, with their arguments. -/
inductive Entry where
  | scheduleTransparent (op : Operation) (delay : UInt256)
  | scheduleShadow (id : OpId) (delay : UInt256)
  | cancel (id : OpId)
  | updateDelay (newDelay : UInt256)
  | updateSecurityCouncil (newCouncil : Address)
  | transferOwnership (newOwner : Address)
  | acceptOwnership
  | renounceOwnership

/-- One call to a non-executing entry point by `caller`: the event and the new state, or `none`
for a revert. -/
def Entry.run (e : Env) (caller : Address) (s : State) : Entry → Option (Ev × State)
  | .scheduleTransparent op delay =>                    -- G:145-149
      if caller ≠ s.owner then none                     -- onlyOwner (Own:35-38, 50-52)
      else (schedule s (e.hashOp op) delay).map fun t => (.scheduled (e.hashOp op) s.now delay, t)
  | .scheduleShadow id delay =>                         -- G:158-161
      if caller ≠ s.owner then none
      else (schedule s id delay).map fun t => (.scheduled id s.now delay, t)
  | .cancel id =>                                       -- G:170-176
      if caller ≠ s.owner then none
      else if !isOperationPending s id then none        -- OperationMustBePending (G:171-173)
      else some (.cancelled id, { s with timestamps := Function.update s.timestamps id 0 })
  | .updateDelay d =>                                   -- G:288-291
      if caller ≠ e.self then none                      -- onlySelf (G:71-76)
      else some (.minDelayChanged s.minDelay d, { s with minDelay := d })
  | .updateSecurityCouncil a =>                         -- G:295-298
      if caller ≠ e.self then none
      else some (.councilChanged s.securityCouncil a, { s with securityCouncil := a })
  | .transferOwnership a =>                             -- Own2:35-38
      if caller ≠ s.owner then none
      else some (.ownershipTransferStarted s.owner a, { s with pendingOwner := a })
  | .acceptOwnership =>                                 -- Own2:52-56, then Own2:44-47
      if s.pendingOwner ≠ caller then none
      else some (.ownershipTransferred s.owner caller, { s with owner := caller, pendingOwner := 0 })
  | .renounceOwnership =>                               -- Own:61-63, then Own2:44-47
      if caller ≠ s.owner then none
      else some (.ownershipTransferred s.owner 0, { s with owner := 0, pendingOwner := 0 })

/-- The checks of `execute` (`instant = false`, G:186-193) or `executeInstant` (`instant = true`,
G:211-218) before the calls: the caller modifier, the predecessor, then ready (resp. pending). -/
def preCheck (e : Env) (instant : Bool) (caller : Address) (s : State) (op : Operation) : Bool :=
  (if instant then caller == s.securityCouncil          -- onlySecurityCouncil (G:79-84)
   else caller == s.owner || caller == s.securityCouncil)  -- onlyOwnerOrSecurityCouncil (G:87-92)
  && predecessorDone s op.predecessor                   -- G:189, G:214
  && (if instant then isOperationPending s (e.hashOp op) else isOperationReady s (e.hashOp op))

/-- The re-check after the calls (G:199-201, G:224-226). -/
def postCheck (instant : Bool) (s : State) (id : OpId) : Bool :=
  if instant then isOperationPending s id else isOperationReady s id

/-- `timestamps[id] = EXECUTED_PROPOSAL_TIMESTAMP` (G:203, G:228). -/
def markDone (s : State) (id : OpId) : State :=
  { s with timestamps := Function.update s.timestamps id 1 }

/-- A finite sequence of successful calls into Governance inside one transaction, each by any
caller: the re-entrant calls an execution's `_execute` makes.  `recheck = false` drops the
re-check after the calls (countermodel only). -/
inductive CallsWith (recheck : Bool) (e : Env) : State → List Ev → State → Prop
  | nil (s : State) : CallsWith recheck e s [] s
  | entry {caller : Address} {s t u : State} {ev : Ev} {evs : List Ev} (x : Entry) :
      x.run e caller s = some (ev, t) → CallsWith recheck e t evs u →
      CallsWith recheck e s (ev :: evs) u
  | exec {caller : Address} {s t u : State} {inner rest : List Ev} (instant : Bool)
      (op : Operation) :
      preCheck e instant caller s op = true →
      CallsWith recheck e s inner t →
      (recheck = true → postCheck instant t (e.hashOp op) = true) →
      CallsWith recheck e (markDone t (e.hashOp op)) rest u →
      CallsWith recheck e s
        (inner ++ .executed (e.hashOp op) op.predecessor instant t.now :: rest) u

/-- One transaction: a call by an outside caller, or the clock moving forward. -/
inductive TopStepWith (recheck : Bool) (e : Env) : State → List Ev → State → Prop
  | entry {caller : Address} {s t : State} {ev : Ev} (x : Entry) :
      caller ≠ e.self → x.run e caller s = some (ev, t) → TopStepWith recheck e s [ev] t
  | exec {caller : Address} {s t : State} {inner : List Ev} (instant : Bool) (op : Operation) :
      caller ≠ e.self →
      preCheck e instant caller s op = true →
      CallsWith recheck e s inner t →
      (recheck = true → postCheck instant t (e.hashOp op) = true) →
      TopStepWith recheck e s (inner ++ [.executed (e.hashOp op) op.predecessor instant t.now])
        (markDone t (e.hashOp op))
  | tick {s : State} (t : UInt256) : s.now ≤ t → TopStepWith recheck e s [] { s with now := t }

/-- The state the constructor leaves (G:52-64). -/
def initState (admin council : Address) (delay now : UInt256) : State where
  owner := admin
  pendingOwner := 0
  securityCouncil := council
  timestamps := fun _ => 0
  minDelay := delay
  now := now

/-- The constructor's events: `Ownable`'s (Own:28-30), then G:57, G:60, G:63. -/
def ctorEvents (deployer admin council : Address) (delay : UInt256) : List Ev :=
  [.ownershipTransferred 0 deployer, .ownershipTransferred deployer admin,
   .councilChanged 0 council, .minDelayChanged 0 delay]

/-- Reachable states with their logs, from a successful constructor at a clock of at least 2. -/
inductive ReachWith (recheck : Bool) (e : Env) : State → List Ev → Prop
  | init (deployer admin council : Address) (delay now : UInt256) :
      admin ≠ 0 → 2 ≤ now.val →
      ReachWith recheck e (initState admin council delay now)
        (ctorEvents deployer admin council delay)
  | step {s t : State} {log evs : List Ev} :
      ReachWith recheck e s log → TopStepWith recheck e s evs t →
      ReachWith recheck e t (log ++ evs)

/-- A sequence of transactions. -/
inductive TopRunWith (recheck : Bool) (e : Env) : State → List Ev → State → Prop
  | refl (s : State) : TopRunWith recheck e s [] s
  | step {s t u : State} {evs rest : List Ev} :
      TopStepWith recheck e s evs t → TopRunWith recheck e t rest u →
      TopRunWith recheck e s (evs ++ rest) u

/-- The source: the re-check is present. -/
abbrev Calls := CallsWith true
/-- The source's transactions. -/
abbrev TopStep := TopStepWith true
/-- The source's reachable states. -/
abbrev Reach := ReachWith true
/-- The source's runs. -/
abbrev TopRun := TopRunWith true

/-! ## Reading the ghost log -/

/-- What the log says so far: the minimum delay last set, and for each id its outstanding schedule
(time, delay, minimum delay in force when scheduled), cleared by a cancel or an execution. -/
structure Hist where
  delay : UInt256
  sched : OpId → Option (UInt256 × UInt256 × UInt256)

/-- One log entry's effect on `Hist`. -/
def Hist.apply (h : Hist) : Ev → Hist
  | .minDelayChanged _ n => { h with delay := n }
  | .scheduled id t d => { h with sched := Function.update h.sched id (some (t, d, h.delay)) }
  | .cancelled id => { h with sched := Function.update h.sched id none }
  | .executed id _ _ _ => { h with sched := Function.update h.sched id none }
  | _ => h

/-- The history a log describes. -/
def hist (log : List Ev) : Hist := log.foldl Hist.apply ⟨0, fun _ => none⟩

/-- The minimum delay the log last set. -/
def lastDelay (log : List Ev) : UInt256 := (hist log).delay

/-- The id's outstanding schedule in the log: `some (t, d, m)` if it was scheduled at time `t` with
delay `d` while the minimum delay was `m`, and has not since been cancelled or executed. -/
def pendingSched (id : OpId) (log : List Ev) : Option (UInt256 × UInt256 × UInt256) :=
  (hist log).sched id

/-- Whether an entry is an execution of `id`. -/
def Ev.isExecOf (id : OpId) : Ev → Bool
  | .executed i _ _ _ => i == id
  | _ => false

/-- How many times the log records an execution of `id`. -/
def execCount (id : OpId) (log : List Ev) : ℕ := log.countP (Ev.isExecOf id)

/-- The operation state the log predicts for `id` at clock `now`: with no outstanding schedule,
`unset` if never executed and `done` otherwise; with an outstanding schedule at time `t` with delay
`d`, `waiting` before `t + d` and `ready` from then on. -/
def stateFromLog (now : UInt256) (id : OpId) (log : List Ev) : OpState :=
  match pendingSched id log with
  | none => if execCount id log = 0 then .unset else .done
  | some (t, d, _) => if now.val < t.val + d.val then .waiting else .ready

end Contracts.Governance
