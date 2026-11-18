# Codegen: Lean-to-Solidity for the bridged-token slice

The first experiment of [CODE_GENERATION.md](../../CODE_GENERATION.md): a
restricted contract language with an executable semantics, a Solidity emitter,
and one program — the bridged-token mint/burn/transfer slice — proved to refine
the existing [`BridgedStandardERC20` model](../Contracts/BridgedStandardERC20/README.md).

| Review | File |
|---|---|
| The language and its interpreter: what each construct *means* | [Lang.lean](Lang.lean) |
| The emitter, with its construct-to-Solidity table and refused shapes | [Emit.lean](Emit.lean) |
| The program, transcribed from the pinned source and OZ v4 | [BridgedTokenSlice/Specs/Program.lean](BridgedTokenSlice/Specs/Program.lean) |
| The representation relation `Rel` and "any successful call" `Step` | [BridgedTokenSlice/Specs/Correspondence.lean](BridgedTokenSlice/Specs/Correspondence.lean) |
| The refinement statements | [BridgedTokenSlice/Properties/Refinement.lean](BridgedTokenSlice/Properties/Refinement.lean) |
| Proofs | [BridgedTokenSlice/Proofs/Refinement.lean](BridgedTokenSlice/Proofs/Refinement.lean) |
| The emitted contract | [solidity/src/generated/BridgedTokenSlice.sol](../../solidity/src/generated/BridgedTokenSlice.sol) |
| Tests against the original | [solidity/README.md](../../solidity/README.md) |

## What is proved

For the **interpreter**, with ABI-valid arguments:

* `deploy_establishes` / `deploy_zero_vault_reverts`: a nonzero vault deploys to
  storage representing the model's empty ledger; a zero vault reverts.
* `mint_refines`, `burn_refines`, `transfer_refines`: **both directions** — the
  model rejects iff the program reverts, and on acceptance the program reaches a
  related state with exactly the logs and return value stated. A forward
  simulation alone would admit an always-reverting implementation; this does not.
* `views_exact`: the getters return the represented values and change nothing.
* `simulation`: every successful call, to any function, by any caller, is
  matched by a finite run of model steps — an instance of
  [`Core/Simulation.lean`](../Core/Simulation.lean), whose type fixes no bound.
  `call_matches_at_most_one_step` and `simulation_at_most_one_step`
  (`BridgedTokenSlice/Properties/AtMostOneStep.lean`) state the bound: no step or
  exactly one.
* `reachable_ledger`: in every storage reachable from a deployment, the balances
  of all `2^160` addresses sum to the supply slot and the vault is unchanged.
  Obtained from the model's proof by `safety_transfer`, not reproved.

The model's `WellFormed` is what shows the source's `unchecked` arithmetic does
not wrap: the proofs are the place where `SOL-ARITH` is discharged for this
slice, at the level of the interpreter.

## What is not proved

* **`GEN-EMIT`.** That the printed Solidity behaves as the interpreter says is
  trusted, mitigated by the one-construct-one-line emitter, `solc` as its type
  checker, and the Lean-generated vectors in `solidity/`. There is no Solidity
  semantics in this package to prove it against.
* Anything about the **original** contract's bytecode. The tests compare it on
  the covered inputs; no theorem mentions it.
* `BUILD-*` and `VM-*` for either contract.

## The vault slice on L1 at draft/v0.35.0, and the per-chain balance cap

[VaultPreparationSlice/Specs/L1PerChainCapAtV35.lean](VaultPreparationSlice/Specs/L1PerChainCapAtV35.lean)
re-pins the vault preparation slice to era-contracts `draft/v0.35.0` at `b17415d20` (every
cited file is identical at `d9f6789`). The code `vaultProgram` and `tokenProgram` transcribe is
unchanged there apart from renames. What changed is L1's `_handleBridgeToChain`: for a bridged
token it now adds the amount to the per-chain balance cap's `chainTotalDeposited` under the
destination's tracking key, in checked arithmetic. The same file models the rest of the cap as
`CapStepV35`: both hooks, `populateBridgedOut`, `setChainBalanceBackfill`, `markBackfilled`,
`moveChainBalanceToInteropPool` and `initializeUpgrade`, with free interop answers per step.

| Review | File |
|---|---|
| The v35 hook, the cap's functions and runs, the pool key | [VaultPreparationSlice/Specs/L1PerChainCapAtV35.lean](VaultPreparationSlice/Specs/L1PerChainCapAtV35.lean) |
| The statements | [VaultPreparationSlice/Properties/L1PerChainCapAtV35.lean](VaultPreparationSlice/Properties/L1PerChainCapAtV35.lean) |
| Proofs | [VaultPreparationSlice/Proofs/L1PerChainCapAtV35.lean](VaultPreparationSlice/Proofs/L1PerChainCapAtV35.lean) |

What is proved:

* `L1BridgeBurnRefinesAtV35`: the slice's `BridgeBurnRefines` with the v35 L1 hooks, whose
  only hook premise is agreeing metadata (`L1HooksAgreeAtV35`).
  `L1PrepareAtV35IsPinPlusCredit`: for an asset not native to L1, the v35 model preparation
  is the one with the pin's hook plus the deposit credit, and fails when the credit fails;
  `L1HookFailsOnlyOnDepositOverflowAtV35`: the credit fails exactly when the tracked counter
  would overflow, with `Panic(0x11)`. `L1BridgeBurnAtV35IsPinCallPlusCredit` is the same
  comparison for the program call, with no model state: the v35 call is the pin's call plus the
  credit, and reverts with exactly the hook's failure when it fails.
  `L1DepositOverflowWitnessAtV35` gives a represented request whose call succeeds with the
  pin's hook and reverts with `Panic(0x11)` with the v35 hook.
* `L1BridgeBurnCreditsJournalEntryAtV35` and `L1SliceRunCreditsJournalAtV35`: a successful
  call, and any run of the slice, change the cap storage only by crediting each returned amount
  to the destination's tracking key, and never write the vault's storage.
  `L1SliceDepositsBackedByBurnsAtV35`: with the premises of `ReachableJournalBacked`, the
  deposits under any set of keys plus the token's supply never exceed their starting total.
  `L1SliceStepIsCapStepAtV35`: every slice step is one cap step or leaves the cap alone.
* The cap's runs: `PoolNeverOverdrawnV35` (no premise on the owner), `CoveredRunsKeepCapV35`
  (each `markBackfilled` must close a covered chain; `UncoveredCloseBreaksCapV35` shows the
  premise is needed, since the code does not check it), `CappedWithdrawalWithinLimitV35` and
  the exact `CappedWithdrawalSucceedsIffWithinLimitV35`, `PendingWithdrawalUncappedV35`,
  `CapCountersMonotoneV35`, and `InteropPoolKeyOutsideChainIdsV35` for the transcribed pool
  constant.

What is not proved:

* That `_trackedBalance`'s view calls return (`DEP-RESULTS`). The interop answers are an
  input, fixed for a slice run and free for each cap step, so no statement relies on
  `enableInterop` being one-way, and none relates a chain's own counters to the pool's after
  its balance moved. Those results, over a run model of the same function shapes with one-way
  flags, are in `Contracts/L1NativeTokenVault/` topic `InteropPool` (`FlagsMonotone`,
  `PoolDepositIdentity`, `PoolWithdrawalsCovered`, `TotalsOnlyGrow`); `CapCountersMonotoneV35`
  and `PoolNeverOverdrawnV35` here are close to `TotalsOnlyGrow` and `PoolWithdrawalsCovered`
  there, but hold from any state satisfying the invariant, with interop answers free per step.
* That the chains `initializeUpgrade` lists are below `2^48`: a premise of that step.
* The native-token and base-token branches of `bridgeBurn`, and `bridgeMint` and the recovery
  paths, beyond their hook step; the router's choice of handler.
* Anything about the deployed vault's bytecode or storage layout (`REP-VAULT` stays open).
