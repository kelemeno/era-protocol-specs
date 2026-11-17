import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: the `Governance` timelock, with re-entrant execution

Source: `l1-contracts/contracts/governance/Governance.sol` at `feat/upgrade-simplification`
commit `e561b9cc2` (the commit `../ChainTypeManager/` models). The file is byte-identical at
the era-contracts pin `c67894b9`. `IGovernance.sol` and `Common.sol` are in the same
directory. `Ownable2Step` is OpenZeppelin `release-v4.9` (`lib/openzeppelin-contracts-v4`, a
submodule that is not checked out in either tree; read at v4.9.6). Line numbers below are
`Governance.sol` unless another file is named.

**This file is definitions only.** The results are in
`EraSpec.Contracts.Governance.Properties.Timelock` and are proved in
`EraSpec.Contracts.Governance.Proofs.Timelock`.

## Storage

    contract Governance is IGovernance, Ownable2Step                          // :30
    uint256 internal constant EXECUTED_PROPOSAL_TIMESTAMP = uint256(1);       // :32
    address public securityCouncil;                                           // :36
    mapping(bytes32 operationId => uint256 executionTimestamp) public timestamps; // :42
    uint256 public minDelay;                                                  // :45

plus `Ownable`'s `_owner` and `Ownable2Step`'s `_pendingOwner`. `timestamps[id]` is the whole
per-operation state: `0` = not created, `1` = executed, anything else = the time it becomes
ready (:38-41). The constructor (:52-64) sets the owner (nonzero, :53-55), the council (may
be zero) and `minDelay`; every `timestamps` slot starts at 0.

## The operation state (:100-132)

    function getOperationState(bytes32 _id) public view returns (OperationState) {
        uint256 timestamp = timestamps[_id];
        if (timestamp == 0) return OperationState.Unset;
        else if (timestamp == EXECUTED_PROPOSAL_TIMESTAMP) return OperationState.Done;  // :125
        else if (timestamp > block.timestamp) return OperationState.Waiting;
        else return OperationState.Ready; }
    isOperation = state != Unset; isOperationPending = Waiting || Ready;
    isOperationReady = Ready; isOperationDone = Done

## The entry points

    scheduleTransparent(op, delay)  onlyOwner   _schedule(hashOperation(op), delay)   // :145-149
    scheduleShadow(id, delay)       onlyOwner   _schedule(id, delay)                  // :158-161
    _schedule(id, delay):                                                             // :245-254
        if (isOperation(id)) revert OperationExists();
        if (delay < minDelay) revert InvalidDelay();
        timestamps[id] = block.timestamp + delay;          // checked: reverts on overflow
    cancel(id)                      onlyOwner                                         // :170-176
        if (!isOperationPending(id)) revert; delete timestamps[id];
    execute(op)                     onlyOwnerOrSecurityCouncil                        // :186-205
        id = hashOperation(op); _checkPredecessorDone(op.predecessor);                // :187-189
        if (!isOperationReady(id)) revert;                                            // :191-193
        _execute(op.calls);                                                           // :196
        if (!isOperationReady(id)) revert;      // the re-check                       // :199-201
        timestamps[id] = EXECUTED_PROPOSAL_TIMESTAMP; emit OperationExecuted(id);     // :203-204
    executeInstant(op)              onlySecurityCouncil                               // :211-230
        the same with isOperationPending in both checks (:216-218, the re-check :224-226)
    _execute(calls): for each call: (ok, ret) = target.call{value}(data);
                     if (!ok) revert with ret                                         // :258-271
    _checkPredecessorDone(p): if (p != 0 && !isOperationDone(p)) revert               // :276-280
    updateDelay(d)                  onlySelf    minDelay = d                          // :288-291
    updateSecurityCouncil(a)        onlySelf    securityCouncil = a                   // :295-298
    receive() external payable {}                                                     // :301
    transferOwnership(a)  onlyOwner  _pendingOwner = a           // Ownable2Step.sol:35-38
    acceptOwnership()     require(pendingOwner() == msg.sender);
                          _transferOwnership(msg.sender)          // Ownable2Step.sol:52-56
    renounceOwnership()   onlyOwner  _transferOwnership(address(0))   // Ownable.sol:61-63
    _transferOwnership(a): delete _pendingOwner; _owner = a
                                      // Ownable2Step.sol:44-47, Ownable.sol:78-82

The modifiers are at :71-92: `onlySelf` is `msg.sender == address(this)`, `onlySecurityCouncil`
is `msg.sender == securityCouncil`, `onlyOwnerOrSecurityCouncil` is either. `hashOperation` is
`keccak256(abi.encode(op))` (:234-236).

## Where execution can re-enter

Only inside `_execute` (:263). There Governance calls each target in turn:

* a **foreign target** runs arbitrary code. It may call any Governance entry point, any
  number of times, directly or through other contracts. The caller Governance then sees is
  that contract, never Governance itself. The call may come from the owner's or the council's
  own contract if the target reaches it: this model treats the owner and the council as
  **abstract contracts** that may call back at any point (a stated boundary). The target may
  catch a failing call or let it propagate.
* a **self-call** (`target == address(this)`) runs the Governance function its calldata
  selects, with `msg.sender == address(this)`. This is the only way to pass `onlySelf`.

## Modelling choices

* **The external world is data** (the `InteropHandlerBase/Reentrancy` pattern). `Callee` is
  what one call's target does, as a finite tree: the Governance entry points it calls, as
  whom, the targets of the calls each of those executions delivers in turn, and whether it
  catches each failure. `exec` is deterministic given that tree, and the results quantify
  over every tree, so every re-entrant behaviour at every depth is covered. A target whose
  later choices depend on how an earlier call went is the tree of the choices it actually
  made: the semantics is deterministic, so that outcome is fixed by the tree. A `Callee.calls`
  node whose caller is Governance itself describes no real behaviour (a foreign contract
  cannot make `msg.sender` equal Governance) and reverts. A `Callee.selfCall` tree at a
  foreign target returns, so it adds nothing beyond `returns`.
* **A self-call's calldata is decoded by a parameter** `Env.dec` (`SOL-ABI`): the results
  hold for every decoder. A view function, `hashOperation` and `receive()` decode to `noop`;
  calldata matching no selector decodes to `invalid` (the contract has no fallback, so it
  reverts). A self-call that executes an operation takes the targets of that operation's
  calls from its `Callee.selfCall` tree.
* **The hash is a parameter** `Env.H : Operation → OpId`. No result assumes anything of it;
  the transparent-binding result names the collision it allows on two logged operations.
* **Fuel bounds the depth.** `exec v E τ n` runs a frame with depth and loop budget `n`;
  when it runs out the frame reverts (gas, call depth). The results hold for every `n`.
* **A revert is `none`, and leaves nothing.** A reverted frame's writes and logs are undone,
  including those of its nested frames; its caller continues from the state before the call
  when it catches the failure, and reverts too otherwise. A reverted transaction leaves the
  state and the log as they were (`commit`). This is `VM-REVERT` as modelled.
* **The log is the committed trace.** It has the contract's events, some with ghost fields,
  and one ghost entry. A schedule records the block time and the minimum delay then in force
  (the event has the id and the delay; the payload too for a transparent schedule). An
  execution records the executed `Operation` (the transaction's calldata), the block time and
  the path. The ghost entry `delivered id i` records that call `i` of an execution of `id`
  returned to Governance in a committed frame. A frame's log lists each delivery followed by
  the log of the frames nested in it, in execution order.
* **Ownership is `Ownable2Step` as written.** `transferOwnership` overrides `Ownable`'s, so it
  has no zero-address check; a new nomination replaces the old one; `acceptOwnership` and
  `renounceOwnership` clear the nomination. The owner may be any address, Governance's own
  included: then only a self-call passes `onlyOwner`.
* **Time** is `block.timestamp`, fixed for a transaction (`Tx.time`). Times along a sequence
  of transactions are not assumed ordered (`TimesMonotone` is available where wanted);
  none of the safety results needs it.
* **Numbers.** Times, delays and timestamps are `ℕ`. The checked addition at :253 is the guard
  `τ + delay < 2^256` ("overflow of τ+d means no step").
* **Reject-only checks omitted**: the `value` of a call (payable/non-payable checks and
  Governance's balance) and the owner-zero check of the constructor. Omitting a check that
  can only revert only adds runs. Events other than the ones listed carry no state.
* **Transactions.** A transaction's caller is any address but Governance's own (a contract
  sends no transactions); `submit` ignores a transaction from Governance's address.
* **A variant for the countermodel.** `Variant.noRecheck` removes the two re-checks
  (:199-201, :224-226); everything else is shared with the source (`Variant.deployed`).
-/

namespace Contracts.Governance

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- An operation id (`bytes32`); `0` means "no predecessor" (:277). -/
abbrev OpId := UInt256

/-- `EXECUTED_PROPOSAL_TIMESTAMP` (:32): the timestamp value that means "executed". -/
def EXECUTED : ℕ := 1

/-- `Call` (`Common.sol:9-13`). The calldata is an opaque value: only Governance's own
decoding of a self-call reads it (`Env.dec`). -/
structure Call where
  /-- `target`. -/
  target : Address
  /-- `value`, in wei (not modelled beyond being part of the operation). -/
  value : ℕ
  /-- `data`, as an opaque value. -/
  data : ℕ
deriving DecidableEq

/-- `IGovernance.Operation` (`IGovernance.sol:27-31`). -/
structure Operation where
  /-- `calls`. -/
  calls : List Call
  /-- `predecessor`: the id of an operation that must be done first, or `0`. -/
  predecessor : OpId
  /-- `salt`. -/
  salt : OpId
deriving DecidableEq

/-- A call of one of Governance's external functions, as its calldata selects it. -/
inductive GovEntry
  /-- `scheduleTransparent(op, delay)` (:145-149). -/
  | scheduleTransparent (op : Operation) (delay : ℕ)
  /-- `scheduleShadow(id, delay)` (:158-161). -/
  | scheduleShadow (id : OpId) (delay : ℕ)
  /-- `cancel(id)` (:170-176). -/
  | cancel (id : OpId)
  /-- `execute(op)` (:186-205). -/
  | execute (op : Operation)
  /-- `executeInstant(op)` (:211-230). -/
  | executeInstant (op : Operation)
  /-- `updateDelay(d)` (:288-291). -/
  | updateDelay (d : ℕ)
  /-- `updateSecurityCouncil(a)` (:295-298). -/
  | updateSecurityCouncil (a : Address)
  /-- `transferOwnership(a)` (`Ownable2Step.sol:35-38`). -/
  | transferOwnership (a : Address)
  /-- `acceptOwnership()` (`Ownable2Step.sol:52-56`). -/
  | acceptOwnership
  /-- `renounceOwnership()` (`Ownable.sol:61-63`). -/
  | renounceOwnership
  /-- A view function, `hashOperation`, or `receive()` (:301): succeeds and writes nothing. -/
  | noop
  /-- Calldata that matches no function: reverts (there is no fallback). -/
  | invalid
deriving DecidableEq

/-- `execute(op)` (`instant = false`) or `executeInstant(op)` (`instant = true`). -/
def GovEntry.execution (op : Operation) (instant : Bool) : GovEntry :=
  if instant then .executeInstant op else .execute op

/-- `IGovernance.OperationState` (`IGovernance.sol:16-21`). -/
inductive OperationState
  | Unset
  | Waiting
  | Ready
  | Done
deriving DecidableEq

/-- Governance's storage. -/
structure State where
  /-- `Ownable._owner`. -/
  owner : Address
  /-- `Ownable2Step._pendingOwner`. -/
  pendingOwner : Address
  /-- `securityCouncil` (:36). -/
  council : Address
  /-- `minDelay` (:45). -/
  minDelay : ℕ
  /-- `timestamps` (:42). -/
  ts : OpId → ℕ

/-- The state the constructor leaves (:52-64): owner `admin`, no pending owner, council and
minimum delay as given, every operation `Unset`. -/
def deployState (admin council : Address) (minDelay : ℕ) : State :=
  ⟨admin, 0, council, minDelay, fun _ => 0⟩

/-- `timestamps[id] = t`. -/
def State.setTs (s : State) (x : OpId) (t : ℕ) : State :=
  { s with ts := fun y => if y = x then t else s.ts y }

/-- `getOperationState(id)` at block time `τ` (:121-132). -/
def State.opState (s : State) (τ : ℕ) (x : OpId) : OperationState :=
  if s.ts x = 0 then .Unset
  else if s.ts x = EXECUTED then .Done
  else if s.ts x > τ then .Waiting
  else .Ready

/-- `isOperationPending(id)` (:105-108). -/
def State.isPending (s : State) (τ : ℕ) (x : OpId) : Prop :=
  s.opState τ x = .Waiting ∨ s.opState τ x = .Ready

instance (s : State) (τ : ℕ) (x : OpId) : Decidable (s.isPending τ x) := by
  unfold State.isPending; infer_instance

/-- `_checkPredecessorDone(p)` passes (:276-280). -/
def State.predecessorDone (s : State) (τ : ℕ) (p : OpId) : Prop :=
  p = 0 ∨ s.opState τ p = .Done

instance (s : State) (τ : ℕ) (p : OpId) : Decidable (s.predecessorDone τ p) := by
  unfold State.predecessorDone; infer_instance

/-- No operation is pending: every operation is `Unset` or `Done`. The constructor's state is
one (`deployState`). -/
def NoPending (s : State) : Prop := ∀ x, s.ts x = 0 ∨ s.ts x = EXECUTED

/-- What the model fixes about the deployment. -/
structure Env where
  /-- `address(this)`. -/
  self : Address
  /-- `hashOperation` (:234-236), `keccak256(abi.encode(op))`. Any function. -/
  H : Operation → OpId
  /-- The function a self-call's calldata selects, with its decoded arguments (`SOL-ABI`). -/
  dec : ℕ → GovEntry

/-- A committed log entry. -/
inductive Effect
  /-- `TransparentOperationScheduled(id, delay, op)` (:148, `op = some`) or
  `ShadowOperationScheduled(id, delay)` (:160, `op = none`), with the block time and the
  `minDelay` in force (ghost). -/
  | scheduled (id : OpId) (time delay minDelay : ℕ) (op : Option Operation)
  /-- `OperationCancelled(id)` (:175). -/
  | cancelled (id : OpId)
  /-- Call `i` of an execution of operation `id` returned successfully (:263-269). Ghost. -/
  | delivered (id : OpId) (i : ℕ)
  /-- `OperationExecuted(id)` (:204, :229), with the executed operation (the calldata), the
  block time, and whether it was `executeInstant` (ghost). -/
  | executed (id : OpId) (op : Operation) (time : ℕ) (instant : Bool)
  /-- `ChangeMinDelay(old, new)` (:289). -/
  | minDelayChanged (old new : ℕ)
  /-- `ChangeSecurityCouncil(old, new)` (:296). -/
  | councilChanged (old new : Address)
  /-- `OwnershipTransferStarted(owner, newOwner)` (`Ownable2Step.sol:37`). -/
  | ownershipTransferStarted (newOwner : Address)
  /-- `OwnershipTransferred(old, new)` (`Ownable.sol:81`). -/
  | ownershipTransferred (newOwner : Address)
deriving DecidableEq

/-- What one call's target does, from the moment Governance calls it (:263) until it
returns. -/
inductive Callee
  /-- Returns successfully. -/
  | returns
  /-- Reverts (or runs out of gas). -/
  | reverts
  /-- Calls Governance's entry point `e` with `msg.sender = caller` (itself, or a contract it
  reaches, such as the owner's or the council's); `inner` are the targets of the calls that
  frame delivers, if it executes an operation. If that frame reverts, the target either
  catches the failure (`caught`) and goes on from the state before the call, or reverts.
  Then it goes on as `next`. -/
  | calls (caller : Address) (e : GovEntry) (inner : List Callee) (caught : Bool) (next : Callee)
  /-- At a call whose target is Governance itself: the targets of the calls that the decoded
  function delivers, if it executes an operation. At a foreign target it returns. -/
  | selfCall (inner : List Callee)

/-- The nested targets a `selfCall` tree supplies. -/
def Callee.selfInner : Callee → List Callee
  | .selfCall inner => inner
  | _ => []

/-- What runs: an entry point called by `caller`, the call loop of an execution, or a foreign
target. -/
inductive Frame
  /-- Entry point `e` called with `msg.sender = caller`; `callees` are the targets of the
  calls it delivers, in order (a missing one returns). -/
  | entry (caller : Address) (e : GovEntry) (callees : List Callee)
  /-- `_execute` of operation `id` delivering `cs`, numbered from `i`. -/
  | calls (id : OpId) (i : ℕ) (cs : List Call) (callees : List Callee)
  /-- One call's foreign target. -/
  | target (c : Callee)

/-- The frame one call of `_execute` runs (:263): the selected Governance function, with
Governance as the caller, for a self-call; the target's code otherwise. -/
def callFrame (E : Env) (c : Call) (t : Callee) : Frame :=
  if c.target = E.self then .entry E.self (E.dec c.data) t.selfInner else .target t

/-- Where the re-checks are. -/
inductive Variant
  /-- The source: both executions re-check after `_execute` (:199-201, :224-226). -/
  | deployed
  /-- Countermodel: the two re-checks removed. -/
  | noRecheck
deriving DecidableEq

/-- `_schedule(id, delay)` at block time `τ` (:245-254), for an operation whose payload is
`op` (transparent) or unpublished (`none`, shadow). -/
def schedule (τ : ℕ) (s : State) (x : OpId) (d : ℕ) (op : Option Operation) :
    Option (State × List Effect) :=
  if s.opState τ x = .Unset ∧ s.minDelay ≤ d ∧ τ + d < UInt256.size then
    some (s.setTs x (τ + d), [.scheduled x τ d s.minDelay op])
  else none

/-- **The semantics.** `exec v E τ n f s` runs frame `f` from state `s` at block time `τ`
with budget `n`: the state and committed log it leaves, or `none` if it reverts. -/
def exec (v : Variant) (E : Env) (τ : ℕ) : ℕ → Frame → State → Option (State × List Effect)
  | 0, _, _ => none
  | _ + 1, .entry c (.scheduleTransparent op d) _, s =>
      if c = s.owner then schedule τ s (E.H op) d (some op) else none
  | _ + 1, .entry c (.scheduleShadow x d) _, s =>
      if c = s.owner then schedule τ s x d none else none
  | _ + 1, .entry c (.cancel x) _, s =>
      if c = s.owner ∧ s.isPending τ x then some (s.setTs x 0, [.cancelled x]) else none
  | n + 1, .entry c (.execute op) cbs, s =>
      if (c = s.owner ∨ c = s.council) ∧ s.predecessorDone τ op.predecessor ∧
          s.opState τ (E.H op) = .Ready then
        match exec v E τ n (.calls (E.H op) 0 op.calls cbs) s with
        | some (s₂, l) =>
            if v = .noRecheck ∨ s₂.opState τ (E.H op) = .Ready then
              some (s₂.setTs (E.H op) EXECUTED, l ++ [.executed (E.H op) op τ false])
            else none
        | none => none
      else none
  | n + 1, .entry c (.executeInstant op) cbs, s =>
      if c = s.council ∧ s.predecessorDone τ op.predecessor ∧ s.isPending τ (E.H op) then
        match exec v E τ n (.calls (E.H op) 0 op.calls cbs) s with
        | some (s₂, l) =>
            if v = .noRecheck ∨ s₂.isPending τ (E.H op) then
              some (s₂.setTs (E.H op) EXECUTED, l ++ [.executed (E.H op) op τ true])
            else none
        | none => none
      else none
  | _ + 1, .entry c (.updateDelay d) _, s =>
      if c = E.self then some ({ s with minDelay := d }, [.minDelayChanged s.minDelay d])
      else none
  | _ + 1, .entry c (.updateSecurityCouncil a) _, s =>
      if c = E.self then some ({ s with council := a }, [.councilChanged s.council a])
      else none
  | _ + 1, .entry c (.transferOwnership a) _, s =>
      if c = s.owner then some ({ s with pendingOwner := a }, [.ownershipTransferStarted a])
      else none
  | _ + 1, .entry c .acceptOwnership _, s =>
      if c = s.pendingOwner then
        some ({ s with owner := c, pendingOwner := 0 }, [.ownershipTransferred c])
      else none
  | _ + 1, .entry c .renounceOwnership _, s =>
      if c = s.owner then
        some ({ s with owner := 0, pendingOwner := 0 }, [.ownershipTransferred 0])
      else none
  | _ + 1, .entry _ .noop _, s => some (s, [])
  | _ + 1, .entry _ .invalid _, _ => none
  | _ + 1, .calls _ _ [] _, s => some (s, [])
  | n + 1, .calls x i (c :: cs) cbs, s =>
      match exec v E τ n (callFrame E c (cbs.headD .returns)) s with
      | some (s₁, l₁) =>
          match exec v E τ n (.calls x (i + 1) cs cbs.tail) s₁ with
          | some (s₂, l₂) => some (s₂, .delivered x i :: (l₁ ++ l₂))
          | none => none
      | none => none
  | _ + 1, .target .returns, s => some (s, [])
  | _ + 1, .target .reverts, _ => none
  | _ + 1, .target (.selfCall _), s => some (s, [])
  | n + 1, .target (.calls c e inner caught next), s =>
      if c = E.self then none
      else
        match exec v E τ n (.entry c e inner) s with
        | some (s₁, l₁) =>
            match exec v E τ n (.target next) s₁ with
            | some (s₂, l₂) => some (s₂, l₁ ++ l₂)
            | none => none
        | none => if caught then exec v E τ n (.target next) s else none

/-- The commit rule: a transaction that reverts leaves the state and the log as they were
(`VM-REVERT` as modelled). -/
def commit (s : State) : Option (State × List Effect) → State × List Effect
  | some r => r
  | none => (s, [])

/-- A submitted transaction. -/
structure Tx where
  /-- `msg.sender` (`tx.origin` or the contract that sends the call). -/
  caller : Address
  /-- `block.timestamp`. -/
  time : ℕ
  /-- The depth and loop budget. -/
  fuel : ℕ
  /-- The entry point called. -/
  entry : GovEntry
  /-- The targets of the calls it delivers, in order. -/
  callees : List Callee

/-- One transaction: the state after it and what it committed. A transaction cannot come
from Governance's own address. -/
def submit (v : Variant) (E : Env) (s : State) (t : Tx) : State × List Effect :=
  if t.caller = E.self then (s, [])
  else commit s (exec v E t.time t.fuel (.entry t.caller t.entry t.callees) s)

/-- A sequence of transactions: the final state and the committed log, in order. -/
def submitAll (v : Variant) (E : Env) : State → List Tx → State × List Effect
  | s, [] => (s, [])
  | s, t :: ts =>
      ((submitAll v E (submit v E s t).1 ts).1,
        (submit v E s t).2 ++ (submitAll v E (submit v E s t).1 ts).2)

/-- Block times never decrease along the sequence. -/
def TimesMonotone (txs : List Tx) : Prop := (txs.map Tx.time).Pairwise (· ≤ ·)

/-! ## Reading the log -/

/-- What `once-only` counts: a delivery of call `i` of operation `id`, or its execution. -/
inductive RunKey
  | delivered (id : OpId) (i : ℕ)
  | executed (id : OpId)
deriving DecidableEq

/-- The operation a run key belongs to. -/
def RunKey.id : RunKey → OpId
  | .delivered x _ => x
  | .executed x => x

/-- The run key of a delivery or an execution. -/
def Effect.runKey : Effect → Option RunKey
  | .delivered x i => some (.delivered x i)
  | .executed x _ _ _ => some (.executed x)
  | _ => none

/-- The operation a delivery or an execution belongs to. -/
def Effect.runId (e : Effect) : Option OpId := e.runKey.map RunKey.id

/-- A schedule entry's fields. -/
structure SchedRec where
  /-- The block time of the schedule. -/
  time : ℕ
  /-- The delay passed. -/
  delay : ℕ
  /-- `minDelay` when it was scheduled. -/
  minDelay : ℕ
  /-- The published operation (transparent), or `none` (shadow). -/
  op : Option Operation
deriving DecidableEq

/-- The schedule entry of operation `x`, if the effect is one. -/
def Effect.schedOf (x : OpId) : Effect → Option SchedRec
  | .scheduled y t d m o => if y = x then some ⟨t, d, m, o⟩ else none
  | _ => none

/-- The last schedule of operation `x` in a log. -/
def lastSchedule (x : OpId) (l : List Effect) : Option SchedRec :=
  (l.filterMap (Effect.schedOf x)).getLast?

/-! ## Witness data

Governance at address `99`, owner `1`, council `2`, minimum delay `10`. The hash of an
operation is its salt, so distinct salts give distinct ids; the collision witness reuses a
salt. Calldata `1` sent to Governance itself is `updateDelay(100)`, calldata `2` is
`updateSecurityCouncil(3)`; anything else is no function. Foreign targets are `50` and
`51`. -/

/-- The witness deployment: Governance at `99`, `H op = op.salt`, calldata `1` is
`updateDelay(100)` and calldata `2` is `updateSecurityCouncil(3)`. -/
def timelockEnv : Env :=
  ⟨99, fun op => op.salt, fun n =>
    if n = 1 then .updateDelay 100 else if n = 2 then .updateSecurityCouncil 3 else .invalid⟩

/-- Fresh Governance: owner `1`, council `2`, minimum delay `10`. -/
def timelockInit : State := deployState 1 2 10

/-- Fresh Governance with minimum delay `0` (for the sentinel countermodel). -/
def timelockInitZero : State := deployState 1 2 0

/-- One call to the foreign target `50`. -/
def timelockCall50 : Call := ⟨50, 0, 0⟩

/-- An operation (id `12`) with one call to `50`. -/
def timelockPlainOp : Operation := ⟨[timelockCall50], 0, 12⟩

/-- An operation (id `13`) with one call to `50`, whose predecessor is `timelockPlainOp`. -/
def timelockSuccOp : Operation := ⟨[timelockCall50], 12, 13⟩

/-- An operation with the same id `12` as `timelockPlainOp` (the same salt) but a different
call, to `51`: an `H`-collision on two concrete operations. -/
def timelockCollideOp : Operation := ⟨[⟨51, 0, 0⟩], 0, 12⟩

/-- An operation (id `11`) that self-calls `updateDelay(100)`. -/
def timelockRaiseOp : Operation := ⟨[⟨99, 0, 1⟩], 0, 11⟩

/-- An operation (id `15`) whose predecessor `14` is scheduled only by shadow. -/
def timelockSentinelSuccOp : Operation := ⟨[timelockCall50], 14, 15⟩

/-- A transaction. -/
def timelockTx (caller : Address) (time : ℕ) (e : GovEntry) (cbs : List Callee := []) : Tx :=
  ⟨caller, time, 10, e, cbs⟩

/-- A target that calls `e` as `caller`, does not catch a failure, and returns. -/
def timelockCallback (caller : Address) (e : GovEntry) : Callee := .calls caller e [] false .returns

/-- The owner schedules `timelockPlainOp` at time `100` with delay `10`, then executes it at
`110`. -/
def timelockPlainRun : List Tx :=
  [timelockTx 1 100 (.scheduleTransparent timelockPlainOp 10),
    timelockTx 1 110 (.execute timelockPlainOp)]

/-- The owner schedules `timelockPlainOp` and its successor at `100`, then executes both at
`110`, in order. -/
def timelockPredRun : List Tx :=
  [timelockTx 1 100 (.scheduleTransparent timelockPlainOp 10),
    timelockTx 1 100 (.scheduleTransparent timelockSuccOp 10),
    timelockTx 1 110 (.execute timelockPlainOp),
    timelockTx 1 110 (.execute timelockSuccOp)]

/-- From `timelockInitZero`, at time `1`: the owner shadow-schedules id `14` with delay `0`,
which writes `timestamps[14] = 1`; schedules `timelockSentinelSuccOp` with delay `5`; and at
time `6` executes it. -/
def timelockSentinelRun : List Tx :=
  [timelockTx 1 1 (.scheduleShadow 14 0),
    timelockTx 1 1 (.scheduleTransparent timelockSentinelSuccOp 5),
    timelockTx 1 6 (.execute timelockSentinelSuccOp)]

/-- The owner schedules `timelockPlainOp` at `100`; at `110` executes it with a first target
that calls `execute(timelockPlainOp)` again as the owner. -/
def timelockReenterRun : List Tx :=
  [timelockTx 1 100 (.scheduleTransparent timelockPlainOp 10),
    timelockTx 1 110 (.execute timelockPlainOp) [timelockCallback 1 (.execute timelockPlainOp)]]

/-- The owner schedules `timelockPlainOp` at `100`. At `105` the council executes it
instantly, and its first target has the owner cancel it (`cancel(12)` succeeds in its own
frame). Then the council executes it instantly again, with a plain target. -/
def timelockCancelRun : List Tx :=
  [timelockTx 1 100 (.scheduleTransparent timelockPlainOp 10),
    timelockTx 2 105 (.executeInstant timelockPlainOp) [timelockCallback 1 (.cancel 12)],
    timelockTx 2 105 (.executeInstant timelockPlainOp)]

/-- As `timelockCancelRun`, but the first target has the owner cancel the operation and
shadow-schedule it again with delay `10`. -/
def timelockCancelRescheduleRun : List Tx :=
  [timelockTx 1 100 (.scheduleTransparent timelockPlainOp 10),
    timelockTx 2 105 (.executeInstant timelockPlainOp)
      [.calls 1 (.cancel 12) [] false (timelockCallback 1 (.scheduleShadow 12 10))]]

/-- At `100` the owner schedules `timelockRaiseOp` and `timelockPlainOp`, both with the
minimum delay `10`; at `110` executes `timelockRaiseOp`, which raises the minimum delay to
`100`; then executes `timelockPlainOp`, still at `110`. -/
def timelockRaiseRun : List Tx :=
  [timelockTx 1 100 (.scheduleTransparent timelockRaiseOp 10),
    timelockTx 1 100 (.scheduleTransparent timelockPlainOp 10),
    timelockTx 1 110 (.execute timelockRaiseOp),
    timelockTx 1 110 (.execute timelockPlainOp)]

/-- An operation (id `16`) that self-calls `updateSecurityCouncil(3)`. -/
def timelockCouncilOp : Operation := ⟨[⟨99, 0, 2⟩], 0, 16⟩

/-- Ownership and the council. At `100` the owner `1` nominates `5`, and `5` accepts. Then `5`
schedules `timelockCouncilOp`, and at `110` executes it, which makes `3` the council. Finally
`5` renounces ownership. -/
def timelockOwnershipRun : List Tx :=
  [timelockTx 1 100 (.transferOwnership 5),
    timelockTx 5 100 .acceptOwnership,
    timelockTx 5 100 (.scheduleTransparent timelockCouncilOp 10),
    timelockTx 5 110 (.execute timelockCouncilOp),
    timelockTx 5 110 .renounceOwnership]

/-- The owner publishes `timelockPlainOp` (`scheduleTransparent`) at `100`, and at `110`
executes `timelockCollideOp`, which has the same id. -/
def timelockCollideRun : List Tx :=
  [timelockTx 1 100 (.scheduleTransparent timelockPlainOp 10),
    timelockTx 1 110 (.execute timelockCollideOp)]

end Contracts.Governance
