# Governance

A local model of the owner/security-council timelock `Governance.sol`, with its inherited
OpenZeppelin `Ownable2Step`, including what an operation's calls can do by calling back into
Governance. It is an abstract specification and does not establish Solidity correspondence.

## Sources

| File | Pin |
|---|---|
| `l1-contracts/contracts/governance/Governance.sol` | era-contracts `draft/v0.35.0`, `b17415d2068065a4a3e3f0e7a14a2e96f54212e5` |
| `l1-contracts/contracts/governance/IGovernance.sol`, `Common.sol` (types and events) | same |
| `contracts/access/Ownable.sol`, `contracts/access/Ownable2Step.sol` | submodule `lib/openzeppelin-contracts-v4` at `dc44c9f1a4c3b10af99492eed84f83ed244203f6` (release v4.9.6) |

The three era-contracts files are byte-identical at the interop pin `c67894b9`, at `e561b9cc2`
(the commit `../ChainTypeManager/` models), at `draft/v0.35.0` `d9f67890` and at `main`
`70096e2ea`, so every line number in the spec holds at each of them. All of these commits record
the same OpenZeppelin gitlink.

Review it alongside the [assumption register](../../../ASSUMPTIONS.md): `MODEL-GOVERNANCE`, plus
`VM-CALL` (no outside caller is Governance), `VM-REVERT` (a failing call reverts the execution,
and a reverted frame leaves nothing), `SOL-ABI` (how a self-call's calldata selects a function)
and `OPS-CONFIG` (the deployment's admin, council and minimum delay).

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Timelock | [Specs/Timelock.lean](Specs/Timelock.lean) | [Properties/Timelock.lean](Properties/Timelock.lean) | [Proofs/Timelock.lean](Proofs/Timelock.lean) |

Namespace: `Contracts.Governance`. Statements are `Contracts.Governance.Properties.*`; each
proof has the same name without the `Properties` segment.

## What is modelled

All state-changing entry points: `scheduleTransparent`, `scheduleShadow`, `cancel`, `execute`,
`executeInstant`, `updateDelay`, `updateSecurityCouncil`, and the inherited `transferOwnership`,
`acceptOwnership` and `renounceOwnership`, with their guards. Storage is `_owner`,
`_pendingOwner`, `securityCouncil`, `timestamps` and `minDelay`; the constructor's state is
`deployState`. A revert is `none` and leaves nothing.

`execute`/`executeInstant` run the operation's own calls in order (`_execute`). A call to
Governance itself runs the function its calldata selects (a decoder `Env.dec`), with Governance as
the caller: this is the only way past `onlySelf`. A call to any other target runs that target's
behaviour, a finite tree (`Callee`) of calls into Governance's entry points, each as any caller
but Governance (the owner and the council included), at any depth, each failure caught or
propagated. The semantics `exec` is deterministic given the trees; the general results quantify
over every tree, decoder, hash `Env.H` and budget. A `Variant` without the two re-checks exists
only for countermodels.

A transaction has a caller other than Governance and one block time; times across transactions
are not assumed ordered. The run-level results read the committed log: the source's events, the
schedule entry with its block time and the `minDelay` in force, the execution entry with the
executed operation, its block time and its path, plus a ghost entry for each call that returned.

## What to check

**The guards.** `EntryGuards`: each entry point's guard and write, in either variant.
`EntryGuardsWitness` commits every entry point.

**The state is the log.**

- `StateIsLogReplay`: in either variant, the state every committed frame and every sequence of
  transactions leaves is the replay of its log (`replay`, `Effect.apply`).
- `LoggedEntriesPassedTheirChecks`: every logged entry passed its check (`Effect.CheckedAt`) on the
  state its predecessors replay to: schedules found the id `Unset` and had a delay at least the
  stored `minDelay`, which they record; cancels found the id pending; executions of `op` have id
  `H op` and, after the calls, a `Done` or zero predecessor and a pending (for `execute`, ready) id;
  ownership transfers went to the zero address or to the pending owner.
  Witnesses `StateIsLogReplayWitness` and `LoggedEntriesPassedTheirChecksWitness` use runs with
  re-entrant self-calls, cancels and schedules.
- `NothingAfterExecution`: no entry after an execution of an id concerns that id
  (`NothingAfterExecutionWitness`).

**Once only.**

- `OnceOnly` (headline): in the committed log of any sequence of transactions from any state, no
  id is executed twice and no call of an id is delivered twice. `CommittedRunsWereOpen`,
  `DoneIsPermanent` (in either variant).
- `DoneIffExecuted`: when all block times are at least `2`, an id ends `Done` exactly when it was
  `Done` at the start or the log executes it.
- `ExecutionRunsEachCallOnce`: a committed execution delivers each of its calls once, in order,
  then executes its id; re-entrant frames inside it deliver and execute other ids only.

**The re-check.** `ReentrantReexecutionReverts`: if an operation's calls execute its id
re-entrantly, the outer execution reverts, at the latest at its re-check (the NatSpec at
`Governance.sol:197-198`).
Witness: `ReentrantReexecutionWitness`. Countermodels: `WithoutRecheckReexecutes`,
`WithoutRecheckAnyOpRunsTwice` (without the re-checks, every operation with at least one call,
all to other contracts, runs twice from every state where an owner other than Governance may
execute it; in the source that transaction commits nothing).

**The delay and the published payload.** From a state with nothing pending (the constructor's):

- `OutgoingCallsWaitedOrInstant` (headline): every call Governance commits is followed later in
  the log by an execution of its id (the only one, by `OnceOnly`) that was `executeInstant`, which
  only the council may call (`EntryGuards`), or whose last schedule had a delay at least the
  `minDelay` then in force and was made at least that delay before the execution. Witness: both
  cases.
- `OwnerPathWaited`: every `execute` has a schedule of its id earlier in the log, whose delay was
  at least the `minDelay` then in force and which was made at least that delay before.
  `EarlyExecutionIsInstant`: an execution before the ready time was `executeInstant`.
  `ExecutionNotBeforeSchedule`: when block times never decrease, no execution, instant or not,
  is timed before its last schedule.
- `TransparentBinding`: every execution of `op` has id `H op`; if its last schedule was
  transparent, it published `op` or another operation with the same hash, both logged.
  `TransparentCollisionExecutesAnotherOp` shows the collision case.

**Predecessors.** `PredecessorDone`: when all block times are at least `2`, an operation with a
nonzero predecessor runs after an execution of the predecessor, or the predecessor was `Done` at
the start. `PredecessorDoneOrSentinel` drops the time premise and adds the sentinel case.

**Cancelling in flight and raising the delay.** `InFlightCancelNeedsReschedule`: a cancel of an
operation's id from inside its own execution is followed by a new schedule of it in that log, or
the execution reverts and the cancel with it (`InFlightCancelIneffective`: the call loop commits
with the id `Unset`, and the re-check reverts the execution).
`MinDelayChangeKeepsTimestamps` and `DelayRaiseNotRetroactive`: a new minimum delay applies only to
later schedules ("for future operations", `Governance.sol:286`).

**Authority.** `ConfigChangesNeedExecution`: a transaction that changes `minDelay` or the council
is an `execute`/`executeInstant` whose log ends with that execution.
`DeliveriesBelongToExecutions`: every logged delivery of a call of an id is followed in the log by
an execution of that id. `NewOwnerWasNominated`: every ownership transfer to a nonzero address
comes after a nomination of that address (which only the owner can make) with no nomination or
ownership transfer in between; or no nomination or ownership transfer precedes it, and it went
to the start state's pending owner. `NewOwnerWasNominatedWitness` has the nominee accept inside
an execution.

**Enabledness.** `ReadyIsExecutable`: a ready operation whose calls all go to other contracts and
whose predecessor is zero or `Done` is executed by the owner's or the council's `execute`, when
the targets return without calling back. `PendingIsInstantlyExecutable`: the same for a pending
operation and the council's `executeInstant`. Both witnesses use a nonzero `Done` predecessor.

**The sentinel.** `SentinelCollision`: `timestamps = 1` means `Done` (`Governance.sol:38-41`).
A schedule with block time plus delay equal to `1` writes it, so at a block time of `1` with a zero
minimum delay an id becomes `Done` without being executed, and a successor naming it runs. This
needs a block time of at most `1`; the results that exclude it take block times of at least `2`.

No result assumes the operation hash injective: the statements are about operation ids, and two
operations with the same id share its timestamp.

## What is not modelled (open)

- What the operation's calls do outside Governance; call `value`, `msg.value` and ETH balances
  (`execute` and `executeInstant` are `payable`, and there is a `receive()`).
- `hashOperation`'s concrete `keccak256(abi.encode(...))` and the calldata decoding of self-calls.
- The constructor's zero-admin check, events' fields that the log leaves out, and the view
  functions.
- Liveness beyond one-transaction enabledness for calls to other contracts that return: whether
  real targets and self-calls succeed, and gas.
