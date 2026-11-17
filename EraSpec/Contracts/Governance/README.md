# Governance

A local model of the owner/security-council timelock `Governance.sol`, with its inherited
OpenZeppelin `Ownable2Step`. It is an abstract specification and does not establish Solidity
correspondence.

## Sources

| File | Pin |
|---|---|
| `l1-contracts/contracts/governance/Governance.sol` | era-contracts `draft/v0.35.0`, `d9f678900e1bc8286412b78f56d4a9f443983c29` |
| `l1-contracts/contracts/governance/IGovernance.sol`, `Common.sol` (types only) | same |
| `contracts/access/Ownable.sol`, `contracts/access/Ownable2Step.sol` | submodule `openzeppelin-contracts-v4` at `dc44c9f1a4c3b10af99492eed84f83ed244203f6` (the commit the pin records) |

Review it alongside the [assumption register](../../../ASSUMPTIONS.md): `MODEL-GOVERNANCE`, plus
`VM-CALL` (no outside caller is Governance), `VM-REVERT` (a failing call reverts the execution) and
`OPS-CONFIG` (deployment parameters).

## Review order

| Review | File |
|---|---|
| State, `getOperationState`, the entry points with their guards in source order, re-entrant call sequences, transactions, reachability, the ghost log and how it is read | [Specs/Timelock.lean](Specs/Timelock.lean) |
| The fifteen statements | [Properties/Timelock.lean](Properties/Timelock.lean) |
| The invariant `Inv`, its preservation by every call sequence, the named theorems, the concrete runs | [Proofs/Timelock.lean](Proofs/Timelock.lean) |

## What is modelled

All state-changing entry points: `scheduleTransparent`, `scheduleShadow`, `cancel`, `execute`,
`executeInstant`, `updateDelay`, `updateSecurityCouncil`, and the inherited `transferOwnership`,
`acceptOwnership`, `renounceOwnership`, plus the constructor. Storage is `_owner`, `_pendingOwner`,
`securityCouncil`, `timestamps` and `minDelay`; `block.timestamp` is part of the state and only moves
forward between transactions.

`execute`/`executeInstant` make the operation's calls. Those calls can re-enter Governance. The
model allows any finite sequence of successful re-entrant calls, each by any caller (Governance
itself included, which is how the `onlySelf` functions are reached), and nested executions. Then
it applies the source's re-check and marks the operation done. This over-approximates every
target's code, so the safety results hold whatever the operation's calls do.

The run-level results are stated over a ghost log: the source's events, with the block timestamp
added to schedules and executions and the predecessor and kind added to executions.

## What is proved

From one invariant (`Inv`, preserved by every call sequence including nested executions):

* **State is history** (`OperationStateMatchesHistory`): every id's `getOperationState` is what the
  log says.
* **Once** (`DoneIffExecutedOnce`, `DoneIsPermanent`): every id is executed at most once in any run,
  is done exactly when it was executed, and stays done.
* **Timelock** (`ExecutionRespectsTimelock`, `ScheduleRespectsMinDelay`): every execution has an
  outstanding schedule whose delay was at least the minimum delay in force when scheduled. A
  non-instant execution happens at or after schedule time plus delay. Only fresh ids (never pending,
  never executed) are scheduled.
* **Cancel** (`CancelOnlyPending`): only pending, never-executed ids are cancelled.
* **Order** (`PredecessorExecutedFirst`): a nonzero predecessor was executed earlier in the run.
* **Authority** (`CallerAuthority`, `ExecuteAuthority`, `ConfigOnlyThroughExecution`,
  `SelfUpdatesTouchOnlyTheirField`): who may call what. A transaction that changes `minDelay` or the
  council is an execution of an operation, so it went through the timelock or through the council.
  Self-updates leave scheduled timestamps alone.
* **Enabledness** (`ReadyIsExecutable`): a ready operation with a done predecessor can be executed.

Load-bearing checks and witnesses:

* `NoRecheckDoubleExecution`: drop the re-check after the calls (G:197-201) and a re-entrant
  `execute` of the same operation runs it twice. The source comment at G:197-198 is right.
* `LowClockScheduleMarksDone` (internal flag, not a realistic issue): G:40 says timestamp `1` means
  "already executed". At `block.timestamp + _delay = 1` (clock ≤ 1, minimum delay 0), scheduling
  marks an id done without execution, and an operation naming it as predecessor then runs. The
  model's reachable states start at a clock of at least 2; real chains are far above that.
* `TimelockRunSatisfiable`: a concrete run with an owner execution whose call re-enters to change
  `minDelay`, and an instant council execution of a dependent operation before its time.

No property assumes the operation hash injective: every statement is about operation ids. Two
operations with the same id share one timestamp. Executing one marks the other done, which these
id-level statements cover.

## What is not modelled (open)

* What the operation's calls do outside Governance, `msg.value`/ETH balance (`payable`,
  `receive()`), and the link between `_operation.calls` and the re-entrant calls (any sequence is
  allowed).
* `hashOperation`'s concrete `keccak256(abi.encode(...))`.
* Events' exact payloads (the transparent event's operation body) and the view functions.
* Liveness beyond one-step enabledness: whether calls succeed, and gas.
