# EcosystemUpgradeExecutor

Source: `l1-contracts/contracts/upgrades/registry/executors/EcosystemUpgradeExecutor.sol`
(the staged coordinator), `upgrades/GovernanceUpgradeTimer.sol` (the timer its operation
names), `executors/DomainUpgradeExecutorBase.sol` and `executors/CTMUpgradeExecutor.sol` (the
CTM domain's reservation), and `objects/EcosystemUpgradeOperation.sol`. The code lives on branch
`feat/upgrade-simplification` of the zksync-era `contracts` repository.

**This code no longer exists at `e561b9cc2`**, the commit `../ChainTypeManager/` models:

- `f64622022d` (2026-10-14) deleted the three stages, the pending-operation state,
  `GovernanceUpgradeTimer` and `UpgradeStageValidator`;
- `469310c94e` (2026-10-17) deleted the coordinator.

This model is pinned at **`afa407085`** (`afa4070854051db19da27c85ec23dca712a6554b`,
2026-10-14). It is the parent of `f64622022d`, the last commit with the staged coordinator and
its timer, and an ancestor of `e561b9cc2`. Every `file:line` in the spec is at `afa407085`. The
results describe deleted code. They matter only if a coordinator or a timer like this one
returns.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Lifecycle | [Specs/Lifecycle.lean](Specs/Lifecycle.lean) | [Properties/Lifecycle.lean](Properties/Lifecycle.lean) | [Proofs/Lifecycle.lean](Proofs/Lifecycle.lean) |

Namespace: `Contracts.EcosystemUpgradeExecutor`. Statements are
`Contracts.EcosystemUpgradeExecutor.Properties.*`; each certificate has the same name without
the `Properties` segment.

## What to check

**Lifecycle.**

- `StageGuards`: each stage's transcribed guard.
- `StagesMoveForward`: the slot moves only forward. The order is free → `Prepared` →
  `Executed` → free, or from occupied to free by abandonment.
- `SlotEmptyIffStageNone`: the operation slot is empty exactly when the stage is `None`.
- `ReservationTracksSlot`: without `forward`, the CTM domain is reserved for exactly the
  pending operation.
- `Stage0RefusesForeignOrStartedTimer`, `GovernanceTimerPreparesOnce`: a
  `GovernanceUpgradeTimer` starts once. So stage 0 refuses a timer bound to someone else or
  already started, and an operation that names such a timer is prepared at most once.

**The timer.** The coordinator checks only that the manifest's `timer` is nonzero and has
code, and that `startTimer()` and `checkDeadline()` do not revert. It never reads the delay or
the timer's code.

- `ExecutionWaitsForTheNamedTimer` (headline): if the named timer is a `GovernanceUpgradeTimer`
  with `INITIAL_DELAY = d`, every `stage1` comes at least `d` seconds after the `stage0` that
  prepared it. `TimerBoundIsTight` shows the bound is exact: stage 1 is refused at 9 seconds
  and admitted at 10.
- **Countermodel** `ZeroDelayTimerPasses`: a timer with zero delay passes every check, and all
  three stages run at one timestamp. The stage docs accept this
  (`docs/upgrade-stage-lifecycle.md:95-96`). The manifest's field comment says "every
  operation has an execution delay" (`RegistryTypes.sol:190-193`).
- **Countermodel** `PermissiveTimerPasses`: a contract whose fallback does not revert passes
  as the timer.
- **Countermodel** `ForwardAppliesLegBeforeTheDelay`: the delay gates `stage1`, not the CTM leg.
  The coordinator's owner can `forward` `applyOperation` to the reserved CTM executor in the
  block of stage 0.

## Model boundaries

- A revert is the absence of a step. Manifest-hash checks, the CTM leg's own checks, the
  migration pause and overflow are omitted, which only adds runs.
- The core domain's reservation is not modelled. It only adds reverts.
- Executor bindings (`setCTMExecutor`, `setCoordinator`) are fixed.
- Timer code is one of three kinds: a `GovernanceUpgradeTimer`, permissive code, or code on
  which every call reverts. Other stateful timer code is not modelled.
- The CTM executor's own owner can commit transitions through its own `forward`, with no
  coordinator involved. That path is not modelled here, at `afa407085`. At `e561b9cc2`, where
  the coordinator is gone, it is: `../ChainTypeManager/` (`ExecutorForward`,
  `ForwardOfCtmCallsIsARun`) for the version state, and `../RegistryBootstrapMigration/`
  (topic Forward, `ForwardIsARun`) for the authority state. Upgrade timing at `e561b9cc2`
  (the manifest's `upgradeTimestamp`, the `ServerNotifier` gate) is in `../ChainTypeManager/`
  (`UpgradeTiming`), a different mechanism from the deleted timer modelled here.
