# ValidatorTimelock

Source: `l1-contracts/contracts/state-transition/validators/ValidatorTimelock.sol`, its base
`state-transition/AccessControlEnumerablePerChainAddressUpgradeable.sol`, the packed map
`state-transition/libraries/LibMap.sol`, `common/Config.sol:334`
(`MAX_VALIDATOR_TIMELOCK_EXECUTION_DELAY`), and OpenZeppelin `contracts-upgradeable` v4.9.6
(`Ownable2StepUpgradeable`, `OwnableUpgradeable`, `Initializable`; the submodule at `2d081f24`).

The model is pinned at era-contracts `draft/v0.35.0` **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`). `ValidatorTimelock.sol` and the access-control
base are byte-identical at the earlier v35 pin `d9f6789` and at `e561b9cc2`. `main`
(`70096e2ea`) and the interop pin `c67894b9` carry an older `ValidatorTimelock.sol` (one
unbounded ecosystem delay, no per-chain delay, a `precommitSharedBridge` entry point), which is
not modelled. Every `file:line` in the spec is at `b17415d20`.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| Delay | [Specs/Model.lean](Specs/Model.lean) | [Properties/Delay.lean](Properties/Delay.lean) | [Proofs/Delay.lean](Proofs/Delay.lean) |
| Roles | [Specs/Model.lean](Specs/Model.lean) | [Properties/Roles.lean](Properties/Roles.lean) | [Proofs/Roles.lean](Proofs/Roles.lean) |
| Isolation | [Specs/Isolation.lean](Specs/Isolation.lean) | [Properties/Isolation.lean](Properties/Isolation.lean) | [Proofs/Isolation.lean](Proofs/Isolation.lean) |
| Ownership | [Specs/Model.lean](Specs/Model.lean) | [Properties/Ownership.lean](Properties/Ownership.lean) | [Proofs/Ownership.lean](Proofs/Ownership.lean) |
| LibMap | [Specs/LibMap.lean](Specs/LibMap.lean) | [Properties/LibMap.lean](Properties/LibMap.lean) | [Proofs/LibMap.lean](Proofs/LibMap.lean) |

Namespace: `Contracts.ValidatorTimelock`. Statements are
`Contracts.ValidatorTimelock.Properties.*`; each certificate has the same name without the
`Properties` segment. No result takes a hash premise: the role constants are literal values.

## What to check

**Model: each entry point exactly.** Every state-changing entry point of the proxy is a step,
and each has an exact success condition and effect: `ForwardingGuardsExact` (the five
forwarding entry points read only their role's membership bit, because the role constants are
nonzero), `OwnerCallsExact`, `DelaySettersExact`, `RegistryWritesExact`,
`DefaultAdminRoleIsNotTransferable`, `RotationIsItsGrants` (the six wrappers, with the source's
role lists). `CallsTouchOnlyTheirChain`: a call changes no other chain's storage.

**Delay.**

- `ExecutionWaitsForTheDelay` (headline): if batch `i` of chain `c` was last committed through
  the timelock at time `t < 2^32`, a later successful execute of a range containing `i` runs
  at `t + D` or later, `D` the delay enforced for `c` when the execute runs.
  `ExecutionWaitsForEveryEarlierCommit`: the same for every earlier commit, re-commits in
  between allowed when their clocks are at least `t` and below `2^32`.
  `ExecutionWaitsForTheCommitTimeDelay`: with no `initialize`, `setExecutionDelay` or
  `setChainExecutionDelay` in between, `D` can be the delay at commit time, because nothing
  else lowers an enforced delay (`EnforcedDelayGrowsWithoutAnOwnerSetter`).
- `IncreaseStrictlyRaisesItsChain`, `DelayWriters`, `OnlyCommitsWriteTimestamps`: who moves a
  delay or a timestamp.
- `BoundedRuns`, `ExecuteNotBlockedAfterMaxDelay`, `MaxDelayIsAttained`: delays stay at most
  30 days, so the delay check cannot block an executor's call once every batch's stored
  timestamp is 30 days old.
- Boundaries: `OwnerCanShortenAPendingDelay` (the owner may lower a delay between commit and
  execute, as `validators/interfaces/IValidatorTimelock.sol:92-103` documents),
  `ClockPast2106SkipsTheDelay` (the `uint32` timestamp wraps after `2^32` seconds,
  `VT:297-298`), `UnrecordedBatchIsNotDelayed` (a batch never committed through the timelock
  has timestamp `0`, `VT:336-339`), `RecommitAtAnEarlierClock` (the model's per-call clocks are
  unrelated, so the clock premise above is needed there).
- Load-bearing checks: `UncheckedExecuteRunsEarly`, `UncheckedIncreaseLowersTheDelay`,
  `StoredComparisonAdmitsNoRaise` (the comparison of `VT:141-144` against the enforced delay is
  what makes every successful increase strictly raise it).
- Witnesses: `ExecutionWaitsForTheDelayWitness` (non-empty run between commit and execute,
  delay raised from 100 to 200 seconds, execute exactly at `t + 200`), `DelayBoundIsTight`,
  `RecommitWitness` (a revert and a re-commit in between), `DelayWritersWitness`.

**Roles.**

- `ForwardNeedsTheRole`, `RegistryWriters`.
- `RolesTraceToAVerifiedChainAdmin` (headline): once a chain's registry is not empty, some call
  of the run wrote it and was sent by the chain's verified admin (the chain reported a chain id
  the bridgehub mapped to it, and its `getAdmin()` returned the sender).
- `ForwardsOnlyToOnceRegisteredChains` (headline): from fresh storage, the timelock forwards to
  `c` only after such a call. Only that earlier call is constrained; roles persist if `c` is
  later deregistered or changes its admin.
- **Countermodel** `UncheckedLookupGrantsOnUnregisteredChain`: without the bridgehub check of
  `VT:399-402`, an unregistered contract's self-reported admin grants itself `COMMITTER_ROLE`,
  and the timelock then forwards commits to that contract.
- `RoleDelegationWitness`: a delegated admin (`OPTIONAL_COMMITTER_ADMIN_ROLE`) appoints a
  committer, so the trace is to an earlier call.

**Isolation.** `OtherChainsCannotInterfere` (headline): removing every call on other chains
from a successful run leaves a successful run that agrees with it on chain `c` and on the shared
fields, and a run of calls that address `c` or no chain succeeds from any state agreeing with
its start on those (`StepRespectsAgreement`, `OtherChainCallsKeepAgreement`,
`IsolationWitness`).

**Ownership.** `InitializeAtMostOnce`, `OwnerChangesOnlyByHandover`, `OwnerOnlyCalls`,
`RenouncedTimelockOnlyRaisesDelays` (after renouncing, with no call from address `0`, the owner
stays `0` and delays only rise). `ZeroSenderActsAsRenouncedOwner` shows the sender premise is
needed in the model, where `msg.sender` is any word. Witnesses: `HandoverWitness`,
`RenounceWitness`.

**LibMap.** `LibMapGetSet`, `LibMapSetKeepsWords`, `LibMapGetFitsUint32`,
`RecordLoopWritesTheRange`: the bit-level transcription of `LibMap.Uint32Map` is a point update
and the commit loop writes exactly its range. `PackedTimestampsRefine`,
`PackedTimestampsRefineRuns`: the packed storage represents the model's `committedAt` along
every run. Witnesses: `LibMapWitness` (a full slot, a range across two slots),
`PackedTimestampsWitness`.

## Model boundaries

- A revert is the absence of a step. Gas is not modelled: only `_processBatchTo ==
  type(uint256).max`, whose loop never ends, is excluded (`validRange`).
- External reads (`getChainId`, `getAdmin`, `getZKChain`, block time) are a per-call `Env`,
  fixed within one call and unrelated between calls. Whether the forwarded call succeeds is `Env.forwardOk`; the chain
  diamond is not modelled, so neither is its check that a forwarded range matches its batch
  data.
- A call the chain makes back into the timelock during the forwarded call is a later call of
  the run (the forwarded call is the last action of every forwarding entry point).
- `msg.sender` is any word; `RenouncedTimelockOnlyRaisesDelays` takes "no sender is `0`" as a
  premise.
- Not modelled: `MultisigCommitter` and `PermissionlessValidator`, events, view functions,
  upgrades of the timelock proxy, and OpenZeppelin's constructor-time `initializer` disjunct.
